"""Offline tests of the learning progress report (ci/learning/report.py).

The fixtures in ``fixtures/report`` are synthetic (see its README); no provider or network call
is made.
"""

import contextlib
import csv
import hashlib
import io
import json
import os
import re
import shutil
import tempfile
import unittest

from ci.learning import report

FIX = os.path.join(os.path.dirname(os.path.abspath(__file__)), "fixtures", "report")
RICH = os.path.join(FIX, "rich")
POLICY = os.path.join(FIX, "policy.json")
OUTPUTS = ("index.html", "LEARNING.md", "data.json", "generators.csv", "calibrations.csv",
           "comparisons.csv", "activations.csv", "anchors.csv")


def nb(label):
    return "sha256:" + hashlib.sha256(("synthetic:" + label).encode()).hexdigest()


def read_jsonl(name, kind):
    path = os.path.join(FIX, name, kind + ".jsonl")
    with open(path, encoding="utf-8") as fh:
        return [json.loads(line) for line in fh if line.strip()]


def all_record_ids(name):
    ids = set()
    for kind in ("certifications", "calibrations", "contracts", "trials", "comparisons",
                 "activations"):
        path = os.path.join(FIX, name, kind + ".jsonl")
        if os.path.exists(path):
            ids.update(r["record_id"] for r in read_jsonl(name, kind))
    return ids


def comparison(stage, date, role="design"):
    for c in read_jsonl("rich", "comparisons"):
        if c["role"] == role and c["stage"] == stage and c["created_at"].startswith(date):
            return c
    raise AssertionError("no fixture comparison %s %s" % (stage, date))


class ReportCase(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.mkdtemp(prefix="learning-report-test-")

    def tearDown(self):
        shutil.rmtree(self.tmp, ignore_errors=True)

    def build(self, records=RICH, sub="out", **kw):
        out = os.path.join(self.tmp, sub)
        data = report.build_report(records, out, **kw)
        return data, out

    def read(self, out, name):
        with open(os.path.join(out, name), encoding="utf-8") as fh:
            return fh.read()


class TestRichAggregates(ReportCase):
    @classmethod
    def setUpClass(cls):
        cls._tmp = tempfile.mkdtemp(prefix="learning-report-rich-")
        cls.out = os.path.join(cls._tmp, "out")
        cls.data = report.build_report(RICH, cls.out, as_of="2026-11-28", policy=POLICY)
        cls.design = cls.data["roles"]["design"]
        cls.crypt = cls.data["roles"]["cryptanalysis"]

    @classmethod
    def tearDownClass(cls):
        shutil.rmtree(cls._tmp, ignore_errors=True)

    def test_outputs_exist(self):
        for name in OUTPUTS:
            self.assertTrue(os.path.isfile(os.path.join(self.out, name)), name)

    def test_library_counts_multiple_versions_quarantine(self):
        s = self.design["summary"]
        self.assertEqual(s["current_certified_versions"], 3)
        self.assertEqual(s["current_certified_generators"], 2)
        self.assertEqual(s["current_certified_families"], 2)
        self.assertEqual(s["ever_certified_versions"], 5)
        self.assertEqual(s["ever_certified_generators"], 3)
        self.assertEqual(s["ever_certified_families"], 2)
        self.assertEqual(s["current_quarantined_versions"], 1)
        self.assertEqual(s["current_superseded_versions"], 1)
        self.assertEqual(s["rejected_versions"], 1)
        self.assertEqual(s["eligible_versions"], 2)
        self.assertEqual(s["verified_source_nodes"], 5)
        last = self.design["library"]["points"][-1]
        self.assertEqual((last["certified_versions"], last["unique_generators"],
                          last["families"]), (5, 3, 2))
        gens = self.design["generators"]["rows"]
        self.assertEqual(len(gens), 6)  # one row per generator version (incl. rejected)

    def test_diversity_breaks_on_equivalence_change_and_never_sums(self):
        panels = {p["family_id"]: p for p in self.design["diversity"]["panels"]}
        self.assertEqual(set(panels), {"avoid-word", "sum-fam"})
        segs = panels["avoid-word"]["segments"]
        self.assertEqual(len(segs), 2)
        self.assertEqual([p["version"] for p in segs[1]["points"]], [3])
        for seg in segs:
            for p in seg["points"]:
                self.assertIn("certified_lower_bound_bits", p)
        sg = panels["sum-fam"]["segments"][0]["points"][0]
        self.assertEqual((sg["seed_bits"], sg["certified_lower_bound_bits"],
                          sg["required_bits"]), (24, 20, 20))

    def test_difficulty_stale_unavailable_and_profiles(self):
        diff = self.design["difficulty"]
        self.assertEqual((diff["target"], diff["lo"], diff["hi"]), ("0.40", "0.20", "0.60"))
        keys = {(p["profile_id"], p["generator_id"], p["version"]) for p in diff["panels"]}
        self.assertIn(("profile-0001", "aw-basic", 2), keys)
        self.assertIn(("profile-0002", "aw-basic", 2), keys)  # model change: separate panel
        pts = [p for panel in diff["panels"] for p in panel["points"]]
        n0 = [p for p in pts if p["n"] == 0]
        self.assertEqual(len(n0), 1)
        self.assertFalse(n0[0]["available"])
        self.assertIsNone(n0[0]["p_hat"])
        self.assertIsNone(n0[0]["ci_low"])
        self.assertEqual(sum(1 for p in pts if p["state"] == "stale"), 1)
        sel = [panel["selected_level"] for panel in diff["panels"]
               if panel["profile_id"] == "profile-0001" and panel["generator_id"] == "aw-basic"]
        self.assertEqual(sel, [1])
        html = self.read(self.out, "index.html")
        self.assertIn(report.DIFFICULTY_CAPTION, html)
        self.assertIn("unavailable (n=0)", html)

    def test_allocation_counts_infra_and_generation_errors(self):
        rows = self.design["allocation"]["rows"]
        trials = [t for t in read_jsonl("rich", "trials") if t["role"] == "design"]
        self.assertEqual(sum(r["trials"] for r in rows), len(trials))
        self.assertEqual(sum(r["infra_error"] for r in rows),
                         sum(1 for t in trials if t["outcome"] == "infra_error"))
        self.assertEqual(sum(r["generation_error"] for r in rows), 1)
        self.assertEqual(self.design["allocation"]["trials_with_unknown_contract"], [])

    def test_active_notebook_rollback_and_cas(self):
        s = self.design["summary"]
        an = s["active_notebook"]
        self.assertEqual(an["sha256"], nb("design-notebook-1"))
        self.assertEqual((an["sequence"], an["reason"]), (4, "rollback"))
        self.assertEqual((an["bytes"], an["tokens"]), (1500, 500))
        self.assertEqual(s["activations_applied"], 4)
        cas = [i for i in self.data["issues"] if "compare-and-swap" in i["problem"]]
        self.assertEqual(len(cas), 1)
        rows = self.design["compression"]["rows"]
        self.assertEqual([r["reason"] for r in rows],
                         ["bootstrap", "improvement", "compression", "rollback"])
        self.assertTrue(rows[1]["provisional"])  # provisional activation
        self.assertEqual(rows[1]["scope"], "fresh_seed")
        self.assertEqual((rows[2]["tokens"], rows[2]["bytes"]), (300, 900))  # compression
        self.assertLess(rows[2]["tokens"], rows[1]["tokens"])
        self.assertEqual(rows[0]["cap_tokens"], 4096)
        self.assertEqual(rows[0]["cap_bytes"], 32768)

    def test_one_active_notebook_missing_tokenizer_and_infra_failure(self):
        s = self.crypt["summary"]
        self.assertEqual(s["activations_applied"], 1)
        self.assertEqual(s["active_notebook"]["sha256"], nb("crypt-notebook-0"))
        self.assertIsNone(s["active_notebook"]["tokens"])
        self.assertEqual(s["active_notebook"]["tokens_unavailable_reason"],
                         "no tokenizer measurement recorded")
        self.assertEqual(s["evaluations_by_verdict"]["infra_error"], 1)
        self.assertEqual(s["evaluations_failed"], 1)
        groups = self.crypt["pareto"]["groups"]
        self.assertEqual(len(groups), 1)
        self.assertEqual(groups[0]["points"], [])
        self.assertEqual(len(groups[0]["excluded"]), 2)
        md = self.read(self.out, "LEARNING.md")
        self.assertIn("tokens unavailable", md)

    def test_evaluation_counts(self):
        s = self.design["summary"]
        v = s["evaluations_by_verdict"]
        self.assertEqual((v["pass_performance"], v["pass_compression"], v["fail"],
                          v["inconclusive"], v["awaiting_evaluator"], v["infra_error"]),
                         (4, 2, 1, 3, 1, 0))
        self.assertEqual(s["evaluations_pending"], 1)
        self.assertEqual(s["evaluations_failed"], 1)

    def test_paired_statistics_as_recorded(self):
        rec = comparison("confirm", "2026-10-20")
        row = [p for p in self.design["performance"]["points"]
               if p["kind"] == "comparison" and rec["record_id"] in p["record_ids"]][0]
        self.assertEqual((row["n"], row["w"], row["l"]), (30, 10, 2))
        self.assertEqual(row["incumbent_rate"], 8 / 30)
        self.assertEqual(row["candidate_rate"], 16 / 30)
        self.assertEqual(row["delta_hat"], rec["delta_hat"])
        self.assertEqual(row["lower_bound"], rec["lower_bound"])
        self.assertAlmostEqual(row["delta_pp"], 100 * 8 / 30)
        self.assertEqual(row["notes"], [])
        verdicts = [p["verdict"] for p in self.design["performance"]["points"]
                    if p["kind"] == "comparison"]
        self.assertIn("fail", verdicts)  # rejected candidates are shown
        self.assertIn("inconclusive", verdicts)
        waiting = [p for p in self.design["performance"]["points"]
                   if p.get("verdict") == "awaiting_evaluator"][0]
        self.assertIsNone(waiting["incumbent_rate"])  # n = 0 is unavailable, not 0%
        rejected = comparison("screen", "2026-11-01")
        with open(os.path.join(self.out, "comparisons.csv"), encoding="utf-8") as fh:
            rows = list(csv.DictReader(fh))
        hit = [r for r in rows if rejected["record_id"] in r["record_ids"]][0]
        self.assertEqual((hit["verdict"], hit["w"], hit["l"], hit["lower_bound"]),
                         ("fail", "1", "5", "-0.55"))

    def test_pareto_only_comparable_points(self):
        groups = self.design["pareto"]["groups"]
        self.assertEqual(len(groups), 2)
        by_scope = {g["scope"]: g for g in groups}
        fresh = by_scope["fresh_seed"]
        expected = {comparison(stage, date)["record_id"] for stage, date in (
            ("screen", "2026-10-18"), ("confirm", "2026-10-20"), ("screen", "2026-10-26"),
            ("screen", "2026-11-01"), ("confirm", "2026-11-03"))}
        got = {p["record_ids"][0] for p in fresh["points"]}
        self.assertEqual(got, expected)
        disjoint = by_scope["family_disjoint"]
        self.assertEqual({p["record_ids"][0] for p in disjoint["points"]},
                         {comparison("confirm", "2026-10-28")["record_id"]})
        contracts = {c["contract_id"]: c for c in read_jsonl("rich", "contracts")}
        for g in groups:
            digests = set()
            for p in g["points"]:
                c = contracts[p["contract_id"]]
                digests.add((report.sha256_of(c["profile"]), report.sha256_of(c["mixture"]),
                             c["epoch_id"], c["scope"]))
            self.assertEqual(len(digests), 1)
        waiting = comparison("screen", "2026-11-08")["record_id"]
        self.assertIn(waiting, [e["record_ids"][0] for e in self.design["pareto"]["excluded"]])
        # Frontier only from eligible (incumbent or passed) points.
        for g in groups:
            for p in g["points"]:
                if p["on_frontier"]:
                    self.assertIn(p["class"], ("incumbent", "accepted", "provisional"))

    def test_anchor_series_never_spliced(self):
        series = self.design["anchors"]["series"]
        self.assertEqual(len(series), 3)
        a1 = [g for g in series if g["anchor_epoch"] == "anchor-0001"
              and g["profile_id"] == "profile-0001"]
        self.assertEqual(len(a1), 1)
        self.assertEqual([p["record_ids"][0] for p in a1[0]["points"]],
                         [comparison("anchor", "2026-10-22")["record_id"],
                          comparison("anchor", "2026-10-30")["record_id"]])
        p = a1[0]["points"][1]
        self.assertEqual((p["active_rate"], p["baseline_rate"], p["n"]), (0.65, 0.30, 20))
        self.assertEqual(p["active_sha256"], nb("design-notebook-2"))
        self.assertEqual(p["baseline_sha256"], nb("design-notebook-E"))
        self.assertEqual(p["baseline_identified_by"], "contract arm anchor_baseline")
        contracts = {c["contract_id"]: c for c in read_jsonl("rich", "contracts")}
        for g in series:
            for q in g["points"]:
                c = contracts[q["contract_id"]]
                self.assertEqual(report.sha256_of(c["profile"]), g["profile_digest"])
                self.assertEqual(report.sha256_of(c["mixture"]), g["mixture_digest"])
        other = [g for g in series if g["anchor_epoch"] == "anchor-0001"
                 and g["profile_id"] == "profile-0002"]
        self.assertEqual(len(other), 1)
        self.assertEqual([q["record_ids"][0] for q in other[0]["points"]],
                         [comparison("anchor", "2026-11-13")["record_id"]])
        with open(os.path.join(self.out, "anchors.csv"), encoding="utf-8") as fh:
            self.assertEqual(len(list(csv.DictReader(fh))), 4)

    def test_every_point_traces_to_record_ids(self):
        known = all_record_ids("rich")
        count = [0]

        def walk(obj, parent_key=None):
            if isinstance(obj, dict):
                if "record_ids" in obj and parent_key != "summary":
                    ids = obj["record_ids"]
                    self.assertTrue(ids, "empty record_ids in %r" % parent_key)
                    self.assertTrue(set(ids) <= known, "unknown ids under %r" % parent_key)
                    count[0] += 1
                for k, v in obj.items():
                    walk(v, k)
            elif isinstance(obj, list):
                if parent_key in ("points", "rows", "planned"):
                    for item in obj:
                        self.assertIn("record_ids", item, parent_key)
                for item in obj:
                    walk(item, parent_key)

        walk(self.data["roles"])
        self.assertGreater(count[0], 50)
        with open(os.path.join(self.out, "data.json"), encoding="utf-8") as fh:
            self.assertEqual(json.load(fh)["roles"]["design"]["summary"]
                             ["current_certified_versions"], 3)

    def test_html_is_self_contained(self):
        html = self.read(self.out, "index.html")
        self.assertNotIn("http", html)
        self.assertNotRegex(html, r"(?i)<(link|iframe|img|object|embed)\b")
        self.assertNotRegex(html, r"(?i)\bsrc\s*=")
        self.assertNotRegex(html, r"(?i)url\(|@import")
        self.assertEqual(html.count("<script"), 2)
        self.assertIn('id="role-design"', html)
        self.assertIn('id="role-cryptanalysis"', html)
        for sec in ("library", "diversity", "difficulty", "allocation", "performance",
                    "compression", "anchor", "pareto"):
            for role in report.ROLES:
                self.assertIn('id="%s-%s"' % (role, sec), html)
        self.assertIn("Certified</dt>", html)
        self.assertIn("Empirical</dt>", html)
        self.assertIn("Provisional</dt>", html)
        self.assertIn("<table>", html)
        # Filters are hidden without JavaScript (static fallback shows everything).
        self.assertIn('<form class="filters" data-role="design" hidden', html)
        m = re.search(r'<script type="application/json" id="report-data">(.*?)</script>', html,
                      re.S)
        embedded = json.loads(m.group(1))
        with open(os.path.join(self.out, "data.json"), encoding="utf-8") as fh:
            self.assertEqual(embedded, json.load(fh))

    def test_summary_markdown(self):
        md = self.read(self.out, "LEARNING.md")
        self.assertIn("adversary model of every record is classical", md)
        self.assertIn("Nothing in this report certifies post", md)
        self.assertIn("2 unique generators, 2 unique families, 3 versions", md)
        self.assertIn("`%s`" % nb("design-notebook-1"), md)
        self.assertIn("1 pending", md)
        self.assertIn("Last anchor result", md)


class TestDeterminismAndAsOf(ReportCase):
    def test_deterministic_with_as_of(self):
        _, a = self.build(sub="a", as_of="2026-11-28", policy=POLICY)
        _, b = self.build(sub="b", as_of="2026-11-28", policy=POLICY)
        for name in OUTPUTS:
            with open(os.path.join(a, name), "rb") as fa, open(os.path.join(b, name), "rb") as fb:
                self.assertEqual(fa.read(), fb.read(), name)
        data = json.loads(self.read(a, "data.json"))
        self.assertIsNone(data["generated_at"])

    def test_generated_at_without_as_of(self):
        data, _ = self.build()
        self.assertRegex(data["generated_at"], r"^\d{4}-\d\d-\d\dT\d\d:\d\d:\d\dZ$")

    def test_as_of_filters_records(self):
        data, _ = self.build(as_of="2026-10-15", policy=POLICY)
        s = data["roles"]["design"]["summary"]
        self.assertEqual((s["ever_certified_versions"], s["ever_certified_generators"],
                          s["ever_certified_families"]), (4, 3, 2))
        self.assertEqual(s["current_quarantined_versions"], 0)
        self.assertEqual(s["rejected_versions"], 1)
        self.assertEqual(s["evaluations_by_verdict"]["pass_performance"], 0)
        self.assertEqual(s["active_notebook"]["sha256"], nb("design-notebook-0"))
        self.assertGreater(data["inputs"]["certifications.jsonl"]["after_as_of"], 0)

    def test_bad_as_of_rejected(self):
        with self.assertRaises(ValueError):
            self.build(as_of="28/11/2026")

    def test_cli(self):
        out = os.path.join(self.tmp, "cli")
        sink = io.StringIO()
        with contextlib.redirect_stdout(sink), contextlib.redirect_stderr(sink):
            rc = report.main(["--records", RICH, "--out", out, "--as-of", "2026-11-28",
                              "--policy", POLICY])
            bad = report.main(["--records", RICH, "--out", out, "--as-of", "x"])
        self.assertEqual(rc, 0)
        self.assertEqual(bad, 2)
        for name in OUTPUTS:
            self.assertTrue(os.path.isfile(os.path.join(out, name)))


class TestEmptyAndMalformed(ReportCase):
    def check_empty(self, records):
        data, out = self.build(records)
        for role in report.ROLES:
            s = data["roles"][role]["summary"]
            self.assertEqual(s["ever_certified_versions"], 0)
            self.assertIsNone(s["active_notebook"])
            self.assertIsNone(s["last_comparable_paired_result"])
            self.assertEqual(s["evaluations_pending"], 0)
        self.assertEqual(data["issues"], [])
        html = self.read(out, "index.html")
        self.assertIn("No observations", html)
        self.assertNotIn("<svg class=\"chart\"", html)  # nothing invented
        md = self.read(out, "LEARNING.md")
        self.assertIn("Active notebook: none", md)
        with open(os.path.join(out, "generators.csv"), encoding="utf-8") as fh:
            self.assertEqual(len(fh.read().strip().splitlines()), 1)

    def test_empty_fixture(self):
        self.check_empty(os.path.join(FIX, "empty"))

    def test_missing_directory(self):
        self.check_empty(os.path.join(self.tmp, "does-not-exist"))

    def test_malformed_lines_skipped_and_reported(self):
        data, out = self.build(os.path.join(FIX, "malformed"))
        self.assertEqual(data["inputs"]["certifications.jsonl"]["loaded"], 1)
        problems = sorted(i["problem"].split(":")[0] for i in data["issues"])
        self.assertEqual(len(data["issues"]), 8)
        self.assertIn("duplicate record_id", problems)
        self.assertIn("invalid JSON", problems)
        self.assertIn("missing record_id", problems)
        self.assertIn("not a JSON object", problems)
        self.assertIn("missing or unknown role", problems)
        self.assertIn("missing or invalid created_at", problems)
        self.assertEqual(data["roles"]["design"]["summary"]["ever_certified_versions"], 1)
        self.assertIn("Record issues", self.read(out, "index.html"))


class TestHostileLabels(ReportCase):
    def test_escaping(self):
        data, out = self.build(os.path.join(FIX, "hostile"), as_of="2026-11-28")
        html = self.read(out, "index.html")
        for raw in ('<script>alert("g")', "<svg onload", "<img src=x", "<b>bold</b>",
                    "</script><script>alert", 'fam">'):
            self.assertNotIn(raw, html)
        self.assertEqual(html.count("<script"), 2)
        self.assertEqual(html.count("</script>"), 2)
        self.assertIn("&lt;script&gt;alert(&quot;g&quot;)&lt;/script&gt;", html)
        self.assertNotIn("http", html)
        m = re.search(r'<script type="application/json" id="report-data">(.*?)</script>', html,
                      re.S)
        self.assertNotIn("<", m.group(1))
        self.assertEqual(json.loads(m.group(1))["roles"]["design"]["generators"]["rows"][0]
                         ["generator_id"], '<script>alert("g")</script>')
        md = self.read(out, "LEARNING.md")
        self.assertNotIn("<b>", md)
        self.assertNotIn("</script>", md)
        self.assertNotRegex(md, r"(?<!\\)\[x\]\(")
        with open(os.path.join(out, "generators.csv"), encoding="utf-8") as fh:
            row = list(csv.DictReader(fh))[0]
        self.assertEqual(row["reason"], "'=HYPERLINK(\"evil\")")
        self.assertTrue(row["author"].startswith("[x]"))
        with open(os.path.join(out, "activations.csv"), encoding="utf-8") as fh:
            act = list(csv.DictReader(fh))[0]
        self.assertEqual(act["actor"], "'-2+3")
        self.assertEqual(act["scope"], "'@SUM(A1)")
        for name in ("generators.csv", "calibrations.csv", "comparisons.csv",
                     "activations.csv", "anchors.csv"):
            with open(os.path.join(out, name), encoding="utf-8") as fh:
                for r in csv.reader(fh):
                    for cell in r:
                        if cell and cell[0] in "=+@":
                            self.fail("formula-like cell in %s: %r" % (name, cell))
                        if cell.startswith("-") and not re.fullmatch(r"-[0-9.e+-]+", cell):
                            self.fail("formula-like cell in %s: %r" % (name, cell))


if __name__ == "__main__":
    unittest.main()
