"""Canonical JSON, schemas, the record store, DAG sources and the CLI (L15, L33 and plumbing)."""

import contextlib
import io
import json
import unittest
from pathlib import Path

from ci.learning import canon, cli, records as RS, schema, sources
from ci.learning.tests.helpers import (REV, T0, TempCase, calibration, generator_rows,
                                       policy)


class Canon(unittest.TestCase):
    def test_canonical(self):
        self.assertEqual(canon.canonical({"b": 1, "a": [1.5, "é"]}),
                         '{"a":[1.5,"é"],"b":1}'.encode())
        with self.assertRaises(ValueError):
            canon.canonical({"x": float("nan")})

    def test_record_id_ignores_volatile_fields(self):
        r = {"schema": "x", "a": 1, "created_at": "2026-01-01T00:00:00Z"}
        self.assertEqual(canon.record_id(r), canon.record_id(dict(r, created_at="other")))
        self.assertNotEqual(canon.record_id(r), canon.record_id(dict(r, a=2)))

    def test_contract_id(self):
        c = canon.seal({"schema": "sigaba.learning.contract.v1", "x": 1})
        self.assertEqual(c["contract_id"], c["record_id"])
        self.assertEqual(canon.seal(dict(c, created_at="z"))["contract_id"], c["contract_id"])


class Schemas(unittest.TestCase):
    def test_all_schemas_load(self):
        for name in schema.KINDS.values():
            self.assertIsInstance(schema.validate({}, schema.load(name)), list)

    def test_unknown_keyword_rejected(self):
        with self.assertRaises(ValueError):
            schema.validate(1, {"type": "integer", "maximun": 3})

    def test_policy_example_and_bounds(self):
        self.assertEqual(schema.check(policy(), "policy"), [])
        p = policy()
        p["extra"] = 1
        self.assertTrue(schema.check(p, "policy"))
        self.assertTrue(schema.validate(True, {"type": "integer"}))     # bool is not int


class Store(TempCase):
    def test_append_dedupe_and_validate(self):
        pol = policy()
        store = RS.Store(self.tmp / "s")
        calibration(store, pol, "fam-a", "g", 0, 5, 2, "sha256:" + "0" * 64)
        calibration(store, pol, "fam-a", "g", 0, 5, 2, "sha256:" + "0" * 64)   # same content
        self.assertEqual(len(store.read("calibration")), 1)
        calibration(store, pol, "fam-a", "g", 0, 5, 2, "sha256:" + "0" * 64, when=T0 + 1)
        self.assertEqual(len(RS.Store(self.tmp / "s").read("calibration")), 1)  # id stable
        rec = dict(store.read("calibration")[0], n=6)
        with self.assertRaises(RS.RecordError):
            store.append([rec])                              # record_id no longer matches
        with self.assertRaises(RS.RecordError):
            store.append([dict(rec, n=-1)])
        with (self.tmp / "s" / "calibrations.jsonl").open("a") as f:
            f.write('{"bad": 1}\n')
        self.assertTrue(RS.Store(self.tmp / "s").verify())


class Sources(TempCase):
    """L15: verified nodes only, pinned refs, seeded sampling, empty corpus."""

    def make_dag(self):
        d = self.tmp / "dag"
        files = {
            "dag/Theorems/Thm_A_spec.lean": "theorem A.spec : Spec P R u := by sorry",
            "dag/Theorems/Thm_A_spec.json": json.dumps({"name": "A.spec"}),
            "dag/Solutions/A_spec/Sub_main.lean": "theorem solution : True := trivial",
            "dag/Solutions/A_spec/Sub_main.json": json.dumps({"theorem": "A.spec"}),
            "dag/Theorems/Thm_B_attack.lean": "theorem B.attack : Assumption.Attack a p c := by sorry",
            "dag/Theorems/Thm_B_attack.json": json.dumps({"name": "B.attack"}),
            "dag/Solutions/B_attack/Sub_sk.lean": "sketch",
            "dag/Solutions/B_attack/Sub_sk.json": json.dumps({"theorem": "B.attack"}),
            "dag/Definitions/Def_C.lean": "def C := 1",
            "dag/Definitions/Def_D.lean": "def D := 1",
            "dag/Theorems/Thm_E_open.lean": "theorem E.open : True := by sorry",
            "dag/Theorems/Thm_E_open.json": json.dumps({"name": "E.open"}),
        }
        for p, t in files.items():
            (d / p).parent.mkdir(parents=True, exist_ok=True)
            (d / p).write_text(t)
        recs = self.tmp / "recs"
        recs.mkdir()
        rows = [{"kind": "theorem", "name": "A.spec", "status": "OK", "path": "x"},
                {"kind": "solution", "theorem": "A.spec", "status": "ACCEPTED",
                 "path": "dag/Solutions/A_spec/Sub_main.lean", "proof_type": "prove"},
                {"kind": "theorem", "name": "B.attack", "status": "OK"},
                {"kind": "solution", "theorem": "B.attack", "status": "SKETCH_ACCEPTED",
                 "path": "dag/Solutions/B_attack/Sub_sk.lean"},
                {"kind": "definition", "status": "OK", "path": "dag/Definitions/Def_C.lean"},
                {"kind": "theorem", "name": "E.open", "status": "OK"}]
        (recs / "env-2.jsonl").write_text("".join(json.dumps(r) + "\n" for r in rows))
        return d, recs

    def test_corpus_and_sample(self):
        d, recs = self.make_dag()
        nodes = sources.corpus(d, recs, "env-2", "f" * 40)
        ids = {n["node_id"] for n in nodes}
        self.assertEqual(ids, {"theorem:A.spec", "solution:A_spec/Sub_main", "definition:C"})
        roles = {n["node_id"]: n["role_class"] for n in nodes}
        self.assertEqual(roles["theorem:A.spec"], "design")
        s1 = sources.sample(nodes, "design", 7, 2)
        self.assertEqual(s1, sources.sample(nodes, "design", 7, 2))     # seeded
        self.assertEqual(s1["status"], "ok")
        self.assertTrue(all(r["commit"] == "f" * 40 and r["content_sha256"].startswith("sha256:")
                            for r in s1["roots"]))
        self.assertEqual(sources.sample([], "design", 1)["status"], "empty_corpus")
        ref = {k: s1["roots"][0][k] for k in ("node_id", "commit", "content_sha256")}
        self.assertEqual(sources.ref_problems([ref], nodes), [])
        self.assertTrue(sources.ref_problems([dict(ref, content_sha256="sha256:" + "0" * 64)],
                                             nodes))
        self.assertTrue(sources.ref_problems([dict(ref, node_id="theorem:E.open")], nodes))
        self.assertEqual(sources.corpus(d, None, "env-2", "f" * 40), [])


def run_cli(args):
    buf = io.StringIO()
    with contextlib.redirect_stdout(buf):
        code = cli.main(args)
    return code, buf.getvalue()


class Cli(TempCase):
    def test_route_decide_labels(self):
        base = self.make_base()
        fetched = self.make_fetched(generator_rows())
        route = self.tmp / "route.json"
        code, out = run_cli(["route", "--base", str(base), "--fetched", str(fetched),
                             "--author", "someone", "--permission", "write", "--pr", "3",
                             "--draft", "false", "--out", str(route)])
        self.assertEqual(code, 0)
        self.assertEqual(json.loads(out)["route"], "generator")
        dec = self.tmp / "decision.json"
        code, out = run_cli(["decide-generator", "--route", str(route), "--base", str(base),
                             "--env", "env-2", "--out", str(dec)])
        d = json.loads(dec.read_text())
        self.assertEqual(d["conclusion"], "failure")           # no certify result
        self.assertFalse(d["automerge"])
        code, out = run_cli(["labels", "--decision", str(dec), "--current",
                             '["learning:rejected"]'])
        self.assertEqual(out, "remove learning:rejected\n")

    def test_evaluate_dry_run_publishes_nothing(self):
        base = self.make_base(notebooks={"design": b""})
        fetched = self.make_fetched([("notebooks/design.md", "added", b"# hi\n")])
        route = self.tmp / "route.json"
        run_cli(["route", "--base", str(base), "--fetched", str(fetched), "--author", "a",
                 "--permission", "admin", "--out", str(route)])
        recs = self.tmp / "recs"
        code, out = run_cli(["evaluate", "--route", str(route), "--fetched", str(fetched),
                             "--base", str(base), "--records", str(recs), "--dry-run",
                             "--publish"])
        res = json.loads(out)
        self.assertEqual(code, 0)
        self.assertTrue(res["dry_run"])
        self.assertEqual(res["published"], [])
        self.assertFalse(recs.exists())
        # without --dry-run and with the evaluator disabled: awaiting_evaluator
        p = policy()
        p["evaluator"] = {"enabled": False, "provider": None, "max_trials_per_run": 0}
        self.set_policy(p)
        code, out = run_cli(["evaluate", "--route", str(route), "--fetched", str(fetched),
                             "--base", str(base), "--records", str(recs)])
        self.assertEqual(json.loads(out)["verdict"], "awaiting_evaluator")

    def test_status_doctor_activate_errors(self):
        base = self.make_base()
        code, out = run_cli(["doctor", "--base", str(base), "--records", str(self.tmp / "r")])
        self.assertIn("checks", json.loads(out))
        code, out = run_cli(["status", "--base", str(base), "--records", str(self.tmp / "r")])
        self.assertEqual(json.loads(out)["adversary_model"], "classical")
        code, out = run_cli(["activate", "--base", str(base), "--records", str(self.tmp / "r"),
                             "--merge-commit", REV, "--actor", "a", "--permission", "write"])
        self.assertEqual(code, 0)
        self.assertEqual(json.loads(out)["results"]["design"]["status"], "unchanged")
        code, out = run_cli(["generator-list", "--base", str(self.tmp / "missing")])
        self.assertEqual(code, 2)
        self.assertIn("error", json.loads(out))

    def test_report_passthrough(self):
        fix = Path(__file__).parent / "fixtures" / "report" / "rich"
        if not fix.is_dir():
            self.skipTest("report fixtures absent")
        code, out = run_cli(["report", "--records", str(fix), "--out", str(self.tmp / "rep"),
                             "--as-of", "2026-12-31"])
        self.assertEqual(code, 0, out)
        self.assertTrue((self.tmp / "rep" / "index.html").is_file())


if __name__ == "__main__":
    unittest.main()
