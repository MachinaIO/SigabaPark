"""Generator certification with a fake Lean, and the generator check decision (L13, L14, L27)."""

import json

from ci.learning import certify as CE, decide as DE, lean_iface as LI, route as RT, sampling
from ci.learning.records import Store
from ci.learning.tests.helpers import REV, FakeLean, TempCase, generator_rows


class Certify(TempCase):
    def setUp(self):
        super().setUp()
        self.make_base()
        self.fetched = self.make_fetched(generator_rows())
        self.route = RT.route(self.base, self.fetched, "someone", "write")
        self.assertEqual(self.route["route"], "generator", self.route["problems"])

    def run_cert(self, lean, seeds=2, rng=None):
        return CE.certify(self.route, self.fetched / "files", self.tmp / "core",
                          self.tmp / "ws", seeds, env="env-2", runner=lean, rng=rng)

    def test_certified(self):
        lean = FakeLean()
        res = self.run_cert(lean)
        self.assertEqual(res["status"], "certified", res["problems"])
        self.assertEqual(len(res["smoke"]), 4)                 # 2 levels x 2 seeds
        check = lean.commands[0]
        # L = manifest levels, k = seed bits, h = the policy's entropy (8), never the manifest's
        self.assertTrue(check.startswith(LI.CHECK_COMMAND))
        self.assertTrue(check.endswith(" 2 16 8"), check)
        # every smoke seed is committed and opens correctly
        ctx = CE.smoke_context(self.route["generator"], REV)
        self.assertTrue(all(sampling.verify_reveal(ctx, i) for i in res["reveal"]))
        # determinism re-check: one extra sample per level
        self.assertEqual(sum(c.startswith(LI.SAMPLE_COMMAND) for c in lean.commands), 6)
        # the decision binds it to the pull request and builds the record
        d = DE.decide(self.route, certify=res, exit_code=0, env="env-2", base=self.base,
                      base_sha="b" * 40, created_at="2026-11-28T00:00:00Z")
        self.assertEqual(d["conclusion"], "success", d["comment"])
        self.assertFalse(d["automerge"])
        self.assertEqual(d["labels"], ["learning:needs-maintainer"])
        cert = d["records"][0]
        self.assertEqual((cert["status"], cert["entropy_bits"], cert["required_bits"]),
                         ("certified", 8, 8))
        Store(self.tmp / "store").append(d["records"])

    def test_lean_rejects(self):
        res = self.run_cert(FakeLean(check={"verdict": "rejected", "problems": ["wrong type"]}))
        self.assertEqual(res["status"], "rejected")
        self.assertEqual(res["smoke"], [])
        d = DE.decide(self.route, certify=res, exit_code=1, env="env-2", base=self.base,
                      created_at="2026-11-28T00:00:00Z")
        self.assertEqual(d["conclusion"], "failure")
        self.assertEqual(d["records"][0]["entropy_bits"], 0)

    def test_sampler_output_must_be_kernel_linked(self):
        # The generator's compiled code lies about its descriptor: the link process rejects it.
        lean = FakeLean(link=lambda level, seed: "1" + seed)
        res = self.run_cert(lean)
        self.assertEqual(res["status"], "rejected")
        self.assertTrue(any("did not confirm" in p for p in res["problems"]), res["problems"])
        self.assertTrue(any(c.startswith(LI.LINK_COMMAND) for c in lean.commands))

    def test_malformed_check_output_fails_closed(self):
        for out in ({"verdict": "ok"}, {"verdict": "certified", "problems": ["x"]},
                    {"verdict": "certified", "problems": "none"},
                    {"verdict": "verified", "problems": []}):
            self.assertEqual(self.run_cert(FakeLean(check=out))["status"], "rejected", out)
        lean = FakeLean()
        lean.check = None                                         # no output file
        self.assertEqual(self.run_cert(lean)["status"], "rejected")

    def test_build_failure_and_timeout(self):
        self.assertEqual(self.run_cert(FakeLean(build_ok=False))["status"], "rejected")
        self.assertEqual(self.run_cert(FakeLean(timeout_on="build"))["status"], "rejected")

    def test_sample_failure_never_replaced(self):
        """L14: a failing seed rejects the version; no other seed is drawn."""
        calls = []

        def sample(level, seed):
            calls.append(seed)
            return None if len(calls) == 2 else "01"
        res = self.run_cert(FakeLean(sample=sample))
        self.assertEqual(res["status"], "rejected")
        self.assertEqual(len(calls), 2)
        self.assertEqual([s["status"] for s in res["smoke"]], ["ok", "failed"])
        self.assertEqual(self.run_cert(FakeLean(timeout_on="sample"))["smoke"][0]["status"],
                         "timeout")

    def test_malformed_and_oversized_descriptors(self):
        self.assertEqual(self.run_cert(FakeLean(sample=lambda l, s: "012"))["status"], "rejected")
        self.assertEqual(self.run_cert(FakeLean(sample=lambda l, s: "1" * 5000))["status"],
                         "rejected")

    def test_nondeterministic_generator(self):
        """L13: the same seed and level must give the same descriptor."""
        n = iter(range(1000))
        res = self.run_cert(FakeLean(sample=lambda l, s: format(next(n), "b")))
        self.assertEqual(res["status"], "rejected")
        self.assertTrue(any("not deterministic" in p for p in res["problems"]))

    def test_tampered_file(self):
        (self.fetched / "files" / self.route["generator"]["dir"] / "Generate.lean").write_text("x")
        res = self.run_cert(FakeLean())
        self.assertEqual(res["status"], "rejected")
        self.assertIn("differs", res["problems"][0])

    def test_decision_binds_result(self):
        """L27: a result about another commit, environment or files is not usable."""
        res = self.run_cert(FakeLean())
        for change in ({"revision": "f" * 40}, {"env": "env-9"},
                       {"files": {k: "sha256:" + "0" * 64 for k in res["files"]}},
                       {"status": "certified", "problems": ["x"]}):
            bad = json.loads(json.dumps(res))
            bad.update(change)
            d = DE.decide(self.route, certify=bad, exit_code=0, env="env-2", base=self.base,
                          created_at="2026-11-28T00:00:00Z")
            self.assertEqual(d["conclusion"], "failure", change)
            self.assertEqual(d["records"], [])
        d = DE.decide(self.route, certify=res, exit_code=137, env="env-2", base=self.base)
        self.assertEqual(d["conclusion"], "failure")
        d = DE.decide(self.route, certify=None, exit_code=None, env="env-2", base=self.base)
        self.assertEqual(d["conclusion"], "failure")
        # tampered smoke seed reveal
        bad = json.loads(json.dumps(res))
        bad["reveal"][0]["seed_bits"] = "0" * 16 if bad["reveal"][0]["seed_bits"] != "0" * 16 \
            else "1" * 16
        d = DE.decide(self.route, certify=bad, exit_code=0, env="env-2", base=self.base)
        self.assertEqual(d["conclusion"], "failure")

    def test_route_decisions(self):
        r = RT.route(self.base, self.fetched, "outsider", "read")
        self.assertEqual(DE.decide(r)["labels"], ["learning:not-accepted"])
        r = RT.route(self.base, self.fetched, "someone", "write", draft=True)
        self.assertEqual(DE.decide(r)["conclusion"], "neutral")
        m = RT.route(self.base, self.make_fetched([("dag/Notes/a.md", "added", b"x")], "m"),
                     "someone", "write")
        self.assertEqual(DE.decide(m)["conclusion"], "success")
        self.assertEqual(DE.label_changes(["learning:rejected", "other"],
                                          ["learning:needs-maintainer"]),
                         [("add", "learning:needs-maintainer"),
                          ("remove", "learning:rejected")])
