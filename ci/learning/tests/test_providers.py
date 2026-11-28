"""The `local-cli` provider: authorization, the solver protocol, and failures as
infrastructure, never as outcomes. No model is called (the scripted fixture solver, and a
missing `claude` executable)."""

from __future__ import annotations

import unittest

from ci.learning import evaluate as EV, providers as P

DESIGN = "SigabaNeo.Benchmark.Fixture.avoidDesignFamily"


def req(notebook: bytes, solver="scripted-fixture", wall=60):
    profile = {"profile_id": "p", "role": "design", "provider": "local-cli", "model": "m",
               "settings": {"solver": solver}, "budget": {"wall_seconds": wall}}
    return EV.SolverRequest("design", profile, notebook, "0" * 64, "avoid-word", DESIGN,
                            "SigabaNeoStd.Benchmarks.Families.AvoidWordDesign", "0110",
                            "target")


class LocalCli(unittest.TestCase):
    def test_authorization(self):
        r = req(b"")
        self.assertFalse(P.LocalCliProvider(env={"PATH": "/usr/bin"}).authorized(r.profile))
        ok = P.LocalCliProvider(env={"PATH": "/usr/bin", P.AUTH_ENV: "authorized"})
        self.assertTrue(ok.authorized(r.profile))
        bad = dict(r.profile, settings={"solver": "/bin/sh"})
        self.assertFalse(ok.authorized(bad))
        self.assertEqual(EV.PROVIDERS["local-cli"]().name, "local-cli")

    def test_scripted_solver_follows_the_notebook(self):
        p = P.LocalCliProvider(env={"PATH": "/usr/bin:/bin", P.AUTH_ENV: "authorized"})
        no = p.solve(req(b"Think hard."))
        self.assertEqual(no.status, "no_answer")
        self.assertIsNone(no.solution)
        yes = p.solve(req(b"Apply avoidDesign_target to the descriptor."))
        self.assertEqual(yes.status, "answered")
        self.assertIn("Target SigabaNeo.Benchmark.Fixture.avoidDesignFamily "
                      "[false, true, true, false]", yes.solution["module_text"])
        self.assertEqual(yes.solution["theorem"], "Answers.Solution.solve")
        self.assertEqual(yes.usage["model_calls"], 1)
        self.assertIsInstance(yes.usage["wall_seconds"], int)    # measured by the runner

    def test_missing_model_cli_is_provider_error(self):
        p = P.LocalCliProvider(env={"PATH": "/nonexistent", P.AUTH_ENV: "authorized"})
        self.assertEqual(p.solve(req(b"x", solver="claude-code")).status, "provider_error")

    def test_unknown_solver_is_provider_error(self):
        p = P.LocalCliProvider(env={"PATH": "/usr/bin", P.AUTH_ENV: "authorized"})
        self.assertEqual(p.solve(req(b"x", solver="nope")).status, "provider_error")

    def test_disabled_policy_never_falls_back(self):
        pol = {"evaluator": {"enabled": True, "provider": "local-cli", "max_trials_per_run": 1}}
        prof = req(b"").profile
        import os
        old = os.environ.pop(P.AUTH_ENV, None)
        try:
            prov, why = EV.provider_for(pol, prof, False)
            self.assertIsNone(prov)
            self.assertIn("not authorized", why)
        finally:
            if old is not None:
                os.environ[P.AUTH_ENV] = old


if __name__ == "__main__":
    unittest.main()
