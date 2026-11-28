"""The trusted evaluator with a mock provider, and activation (L04, L14, L20, L21, L23, L25,
L26, L27, L28, L29, L33)."""

import json

from ci.learning import activation as A, canon, decide as DE, evaluate as EV, \
    notebooks as NB, route as RT, sampling
from ci.learning.records import Store
from ci.learning.tests.helpers import (T0, TempCase, calibration, certify_generator, family,
                                       policy)

OLD = b"old notebook\n"
GOOD = b"GOOD: try reductions first.\n"
GOOD2 = b"GOOD too, other words.\n"


class Sampler(EV.Sampler):
    def __init__(self, fail=False):
        self.calls, self.fail = [], fail

    def sample(self, gen, level, seed):
        self.calls.append((gen["generator_id"], level, seed))
        if self.fail:
            raise EV.GenerationError("boom")
        return f"{level:02b}" + seed


class Verifier(EV.Verifier):
    def __init__(self):
        self.calls = 0

    def verify(self, req, solution):
        self.calls += 1
        ok = solution.get("module_text") == "proof"
        return {"verdict": "accepted" if ok else "rejected",
                "theorem_sha256": "sha256:" + "5" * 64, "certified_value": None}


def usage(**kw):
    u = {"model_calls": 1, "input_tokens": 10, "output_tokens": 10, "wall_seconds": 1,
         "lean_seconds": 1}
    u.update(kw)
    return u


def smart(req):
    """Solves only with a GOOD notebook."""
    if req.notebook.startswith(b"GOOD"):
        return EV.SolverResponse("answered", {"module_text": "proof", "theorem": "t"}, usage(),
                                 "mock-1")
    return EV.SolverResponse("no_answer", None, usage(), "mock-1")


class Fixture(TempCase):
    def setUp(self):
        super().setUp()
        self.setup_state(policy())

    def setup_state(self, pol):
        self.pol = pol
        self.make_base(pol, notebooks={"design": OLD})
        import shutil
        shutil.rmtree(self.tmp / "records", ignore_errors=True)
        self.store = Store(self.tmp / "records")
        self.ref = canon.sha256_bytes(OLD)
        # the notebook already on main is seeded by a maintainer (bootstrap activation)
        self.store.append([A.activate(self.store, self.base, pol, "design", "0" * 40, None, None,
                                      "maint", "admin", "2027-01-01T00:00:00Z",
                                      bootstrap=True)["record"]])
        for fam, gen in (("fam-a", "ga"), ("fam-b", "gb"), ("fam-r", "gr")):
            if any(f["family_id"] == fam for f in pol["families"]):
                certify_generator(self.store, self.base, pol, fam, gen, levels=2)
                calibration(self.store, pol, fam, gen, 0, 5, 2, self.ref)

    def route_for(self, data, rev="a" * 40, name="fetched"):
        f = self.make_fetched([("notebooks/design.md", "modified", data)], name, rev)
        r = RT.route(self.base, f, "someone", "write", pr=7)
        self.assertEqual(r["route"], "notebook", r["problems"])
        return r

    def evaluate(self, data, provider, sampler=None, verifier=None, route=None, publish=True):
        route = route or self.route_for(data)
        res = EV.evaluate_notebook(store=self.store, base=self.base, pol=self.pol, route=route,
                                   candidate=data, provider=provider, provider_note="",
                                   sampler=sampler or Sampler(), verifier=verifier or Verifier(),
                                   clock=lambda: T0, as_of=T0)
        if publish:
            self.store.append(res["records"])
        return res


class Evaluate(Fixture):
    def test_full_pass_family_disjoint(self):
        prov = EV.MockProvider(smart)
        res = self.evaluate(GOOD, prov)
        self.assertEqual(res["verdict"], "pass_performance", res["reason"])
        self.assertEqual(len(prov.calls), 2 * (6 + 20))
        con = {c["stage"]: c for c in self.store.read("contract")}
        self.assertEqual({m["family_id"] for m in con["screen"]["mixture"]}, {"fam-a", "fam-b"})
        self.assertIn("fam-r", con["screen"]["excluded_families"])
        self.assertEqual({m["family_id"] for m in con["confirm"]["mixture"]}, {"fam-r"})
        comp = res["confirm"]
        self.assertEqual((comp["scope"], comp["provisional"], comp["n"], comp["w"]),
                         ("family_disjoint", False, 20, 20))
        self.assertEqual(A.recompute(self.store, comp), [])
        # same task for both arms (seed and descriptor), and both arms saw only their notebook
        trials = self.store.read("trial")
        self.assertEqual({t["notebook_sha256"] for t in trials},
                         {canon.sha256_bytes(OLD), canon.sha256_bytes(GOOD)})
        # independent screen/confirm seeds; reveals open every commitment
        reveals = self.store.read("reveal")
        commits = [i["seed_commitment"] for r in reveals for i in r["items"]]
        self.assertEqual(len(commits), len(set(commits)))
        for r in reveals:
            self.assertTrue(all(sampling.verify_reveal(r["contract_id"], i) for i in r["items"]))
        # the PR check passes but never auto-merges
        d = DE.decide(res_route(self), store=self.store, base=self.base)
        self.assertEqual(d["conclusion"], "success")
        self.assertFalse(d["automerge"])

    def test_screen_not_promising_stops(self):
        prov = EV.MockProvider(smart)
        res = self.evaluate(b"no good, and longer than the old one\n", prov)
        self.assertEqual(res["verdict"], "fail")
        self.assertIsNone(res["confirm"])
        self.assertEqual(len(prov.calls), 12)
        self.assertEqual(len(self.store.read("contract")), 1)

    def test_awaiting_evaluator(self):
        """L21: disabled or unauthorized evaluator: nothing runs, no fallback."""
        pol = policy()
        pol["evaluator"] = {"enabled": False, "provider": None, "max_trials_per_run": 0}
        self.assertIsNone(EV.provider_for(pol, pol["profiles"][0], False)[0])
        self.assertIsNone(EV.provider_for(self.pol, self.pol["profiles"][0], False)[0])  # no adapter
        sampler = Sampler()
        res = self.evaluate(GOOD, None, sampler)
        self.assertEqual(res["verdict"], "awaiting_evaluator")
        self.assertEqual(res["records"], [])
        self.assertEqual(sampler.calls, [])
        d = DE.decide(self.route_for(GOOD), store=self.store, base=self.base)
        self.assertEqual(d["labels"], ["learning:awaiting-evaluator"])
        self.assertEqual(d["conclusion"], "failure")

    def test_infra_retries_bounded(self):
        calls = []

        def broken(req):
            calls.append(1)
            raise RuntimeError("provider down")
        res = self.evaluate(GOOD, EV.MockProvider(broken))
        self.assertEqual(res["verdict"], "infra_error")
        self.assertEqual(len(calls), 4)            # both arms of the pair, one retry each; stop
        comp = res["screen"]
        self.assertEqual((comp["n"], comp["pair_refs"]), (0, []))
        t = self.store.read("trial")[0]
        self.assertEqual((t["outcome"], t["reason"], t["retries"]),
                         ("infra_error", "provider_error", 1))
        # one replacement run is allowed (infra_retries = 1), then no more
        self.evaluate(GOOD, EV.MockProvider(broken))
        n = len(calls)
        res = self.evaluate(GOOD, EV.MockProvider(broken))
        self.assertEqual(len(calls), n)
        self.assertEqual(res["verdict"], "infra_error")

    def test_budget_and_self_report(self):
        """L20: over budget is unsolved; a provider's claim is ignored; partial proofs score 0."""
        def over(req):
            return EV.SolverResponse("answered", {"module_text": "proof", "theorem": "t"},
                                     usage(model_calls=11), "m", claimed_solved=True)

        def liar(req):
            return EV.SolverResponse("answered", {"module_text": "sorry", "theorem": "t"},
                                     usage(), "m", claimed_solved=True)
        for behavior, reason in ((over, "budget_exhausted"), (liar, "invalid_proof")):
            self.setUp()
            res = self.evaluate(GOOD, EV.MockProvider(behavior))
            trials = self.store.read("trial")
            self.assertTrue(all(t["outcome"] == "unsolved" and t["reason"] == reason
                                for t in trials), reason)
            self.assertEqual(res["verdict"], "fail")

    def test_unmeasured_usage_is_infra(self):
        res = self.evaluate(GOOD, EV.MockProvider(lambda r: EV.SolverResponse(
            "answered", {"module_text": "proof"}, {"wall_seconds": 1}, "m")))
        self.assertEqual(res["verdict"], "infra_error")

    def test_generation_error_no_replacement(self):
        """L14: a failed generation is retried on the same seed, never replaced."""
        s = Sampler(fail=True)
        prov = EV.MockProvider(smart)
        res = self.evaluate(GOOD, prov, s)
        self.assertEqual(res["verdict"], "infra_error")
        self.assertEqual(len(s.calls), 2)
        self.assertEqual(len({c[2] for c in s.calls}), 1)
        self.assertEqual(prov.calls, [])
        self.assertEqual(len(res["generation_failures"]), 1)
        rev = self.store.read("reveal")[0]
        self.assertEqual(len(rev["items"]), 1)
        self.assertIsNone(rev["items"][0]["descriptor_bits"])

    def test_idempotent_rerun(self):
        """L33: a decided contract is not run again; records are not duplicated."""
        prov = EV.MockProvider(smart)
        first = self.evaluate(GOOD, prov)
        n = len(prov.calls)
        counts = {k: len(self.store.read(k)) for k in ("trial", "comparison", "contract")}
        second = self.evaluate(GOOD, prov)
        self.assertEqual(len(prov.calls), n)
        self.assertEqual(second["verdict"], first["verdict"])
        self.assertEqual(second["records"], [])
        self.assertEqual({k: len(self.store.read(k)) for k in counts}, counts)
        self.assertEqual(self.store.append(first["records"]), [])

    def test_insufficient_generators(self):
        self.setup_state(policy(families=[family("fam-x")]))
        res = self.evaluate(GOOD, EV.MockProvider(smart))
        self.assertEqual(res["verdict"], "inconclusive")
        self.assertIn("insufficient_generators", res["reason"])

    def test_budget_insufficient(self):
        self.pol["evaluator"]["max_trials_per_run"] = 10
        res = self.evaluate(GOOD, EV.MockProvider(smart))
        self.assertIn("budget_insufficient", res["reason"])

    def test_provisional(self):
        """L26: without a reserved family, fresh-seed confirmation only when authorized."""
        fams = [family("fam-a"), family("fam-b")]
        self.setup_state(policy(families=fams))
        prov = EV.MockProvider(smart)
        res = self.evaluate(GOOD, prov)
        self.assertEqual(res["verdict"], "inconclusive")
        self.assertEqual(len(prov.calls), 12)          # screen only
        pol = policy(families=fams)
        pol["promotion"]["provisional_within_family"] = True
        self.setup_state(pol)
        res = self.evaluate(GOOD, EV.MockProvider(smart))
        self.assertEqual(res["verdict"], "pass_performance")
        self.assertEqual((res["confirm"]["scope"], res["confirm"]["provisional"]),
                         ("fresh_seed", True))

    def test_calibrate(self):
        prov = EV.MockProvider(smart)
        res = EV.calibrate(store=self.store, base=self.base, pol=self.pol, role="design",
                           provider=prov, provider_note="", sampler=Sampler(),
                           verifier=Verifier(), clock=lambda: T0, as_of=T0, budget=12)
        self.assertEqual(res["status"], "done")
        self.store.append(res["records"])
        cals = [r for r in self.store.read("calibration") if r["trial_ids"]]
        self.assertTrue(cals)
        self.assertTrue(all(c["n"] == 4 and c["successes"] == 0 for c in cals))
        self.assertTrue(all(c["eligibility"] in ("uncalibrated", "low_priority") for c in cals))
        res = EV.calibrate(store=self.store, base=self.base, pol=self.pol, role="design",
                           provider=None, provider_note="disabled", sampler=Sampler(),
                           verifier=Verifier())
        self.assertEqual(res["status"], "awaiting_evaluator")

    def test_anchor(self):
        res = EV.anchor(store=self.store, base=self.base, pol=self.pol, role="design",
                        anchor_epoch="anchor-1", provider=EV.MockProvider(smart),
                        provider_note="", sampler=Sampler(), verifier=Verifier(),
                        clock=lambda: T0, as_of=T0, pairs=4)
        self.store.append(res["records"])
        comp = res["comparison"]
        self.assertEqual((comp["stage"], comp["anchor_epoch"], comp["n"]),
                         ("anchor", "anchor-1", 4))
        self.assertEqual(comp["incumbent_sha256"], NB.EMPTY_SHA256)
        self.assertEqual(A.recompute(self.store, comp), [])


def res_route(case):
    return case.route_for(GOOD)


class Activation(Fixture):
    def pass_candidate(self, data, rev, name):
        route = self.route_for(data, rev, name)
        res = self.evaluate(data, EV.MockProvider(smart), route=route)
        self.assertEqual(res["verdict"], "pass_performance")
        return route

    def merge(self, data):
        (self.base / "notebooks" / "design.md").write_bytes(data)

    def activate(self, head, actor="someone", permission="write", **kw):
        return A.activate(self.store, self.base, self.pol, "design", "e" * 40, 7, head, actor,
                          permission, "2027-01-15T08:00:00Z", **kw)

    def test_compare_and_swap(self):
        """L28: two candidates beat the same incumbent; only the first activates."""
        r1 = self.pass_candidate(GOOD, "1" * 40, "f1")
        r2 = self.pass_candidate(GOOD2, "2" * 40, "f2")
        self.merge(GOOD)
        out = self.activate("1" * 40)
        self.assertEqual(out["record"]["reason"], "improvement")
        self.assertEqual(out["record"]["predecessor_sha256"], canon.sha256_bytes(OLD))
        self.store.append([out["record"]])
        # The second PR's check is now stale (incumbent changed): its route is recomputed
        d = DE.decide(self.route_for(GOOD2, "2" * 40, "f3"), store=self.store, base=self.base)
        self.assertEqual(d["conclusion"], "failure")
        self.assertTrue(any("stale" in l for l in d["comment"].splitlines()))
        self.merge(GOOD2)
        with self.assertRaises(A.ActivationError):
            self.activate("2" * 40)
        # Idempotent re-run on the first merge
        self.merge(GOOD)
        self.assertEqual(self.activate("1" * 40)["status"], "unchanged")
        del r1, r2

    def test_head_and_epoch_staleness(self):
        """L04/L28: a new head, a policy or an epoch change invalidates the verdict."""
        self.pass_candidate(GOOD, "1" * 40, "f1")
        comp = [c for c in self.store.read("comparison") if c["stage"] == "confirm"][0]
        inc = canon.sha256_bytes(OLD)
        sha = canon.sha256_bytes(GOOD)
        self.assertEqual(A.verdict_status(self.store, comp, self.pol, sha, inc, "1" * 40),
                         (True, "valid"))
        self.assertIn("head", A.verdict_status(self.store, comp, self.pol, sha, inc,
                                               "3" * 40)[1])
        self.assertIn("candidate", A.verdict_status(self.store, comp, self.pol, "sha256:" +
                                                    "0" * 64, inc, None)[1])
        p2 = json.loads(json.dumps(self.pol))
        p2["epoch"]["id"] = "epoch-0002"
        self.assertIn("stale", A.verdict_status(self.store, comp, p2, sha, inc, None)[1])
        p3 = json.loads(json.dumps(self.pol))
        p3["curriculum"]["min_samples"] = 5
        self.assertIn("policy", A.verdict_status(self.store, comp, p3, sha, inc, None)[1])
        # a merge group (head None) checks the candidate bytes instead
        self.assertTrue(A.verdict_status(self.store, comp, self.pol, sha, inc, None)[0])

    def test_fabricated_comparison_rejected(self):
        """L27: aggregates must follow from complete trial records."""
        self.pass_candidate(GOOD, "1" * 40, "f1")
        comp = dict([c for c in self.store.read("comparison") if c["stage"] == "confirm"][0])
        fake = dict(comp, w=comp["w"] + 1)
        self.assertTrue(A.recompute(self.store, fake))
        fake = dict(comp, pair_refs=comp["pair_refs"][:-1])
        self.assertTrue(A.recompute(self.store, fake))
        fake = dict(comp, pair_refs=comp["pair_refs"] + comp["pair_refs"][:1])
        self.assertTrue(A.recompute(self.store, fake))

    def test_no_evidence_no_activation(self):
        """L29: a merged notebook without evidence does not become active."""
        self.merge(GOOD)
        with self.assertRaises(A.ActivationError):
            self.activate("1" * 40)

    def test_rollback_and_replay(self):
        """L29: authorized rollback is recorded as such; replay is deterministic."""
        self.pass_candidate(GOOD, "1" * 40, "f1")
        self.merge(GOOD)
        self.store.append([self.activate("1" * 40)["record"]])
        self.merge(OLD)
        with self.assertRaises(A.ActivationError):
            self.activate("9" * 40, "someone", "write")
        out = self.activate("9" * 40, "maint", "admin")
        self.assertEqual((out["record"]["reason"], out["record"]["comparison_ids"]),
                         ("rollback", []))
        self.store.append([out["record"]])
        events = self.store.read("activation")
        self.assertEqual(A.replay(events), A.replay(json.loads(json.dumps(events))))
        st = A.replay(events)["design"]
        self.assertEqual((st["active"], st["sequence"]), (canon.sha256_bytes(OLD), 3))
        self.assertTrue(A.consistency(self.store, self.base)["design"]["consistent"])
        with self.assertRaises(A.ActivationError):
            A.replay([events[0], events[2]])               # sequence gap
        bad = dict(events[1], predecessor_sha256=NB.EMPTY_SHA256)
        with self.assertRaises(A.ActivationError):
            A.replay([events[0], bad])                     # compare-and-swap violated

    def test_bootstrap(self):
        """Only a maintainer seeds the first notebook of a role, and only once."""
        first = self.store.read("activation")[0]
        self.assertEqual((first["reason"], first["sequence"], first["actor"]),
                         ("bootstrap", 1, "maint"))
        self.merge(GOOD)
        with self.assertRaises(A.ActivationError):
            self.activate(None, "someone", "write", bootstrap=True)
        with self.assertRaises(A.ActivationError):
            self.activate(None, "maint", "maintain", bootstrap=True)   # not the first event
