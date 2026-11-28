"""Statistics, sampling and the curriculum (L22, L23, L24 statistics side)."""

import unittest
from collections import Counter
from fractions import Fraction

from ci.learning import curriculum as CU, decide as DE, sampling, stats
from ci.learning.tests.helpers import T0, family, policy


class Stats(unittest.TestCase):
    def test_wilson(self):
        self.assertIsNone(stats.wilson(0, 0))                 # n = 0 is not 0%
        lo, hi = stats.wilson(8, 20)
        self.assertAlmostEqual(lo, 0.2188, places=4)
        self.assertAlmostEqual(hi, 0.6134, places=4)
        self.assertEqual(stats.wilson(0, 10)[0], 0.0)

    def test_clopper_pearson_known_values(self):
        # Reference values (exact Clopper-Pearson, one-sided 2.5%): 5/10 -> [0.18709, 0.81291].
        lo, hi = stats.cp_lower(5, 10, "0.025"), stats.cp_upper(5, 10, "0.025")
        self.assertAlmostEqual(lo, 0.1870860, places=6)
        self.assertAlmostEqual(hi, 0.8129140, places=6)
        self.assertAlmostEqual(lo + hi, 1.0, places=10)      # symmetry
        self.assertEqual(stats.cp_lower(0, 10, "0.025"), 0.0)
        self.assertEqual(stats.cp_upper(10, 10, "0.025"), 1.0)
        # x = n: lower bound = a^(1/n); x = 0: upper = 1 - a^(1/n); conservative side.
        self.assertLessEqual(stats.cp_lower(10, 10, "0.025"), 0.025 ** 0.1)
        self.assertGreaterEqual(stats.cp_upper(0, 10, "0.025"), 1 - 0.025 ** 0.1)
        self.assertAlmostEqual(stats.cp_lower(10, 10, "0.025"), 0.025 ** 0.1, places=9)

    def test_cp_union(self):
        self.assertEqual(stats.cp_union(0, 0, 0, "0.05"),
                         {"lower_bound": None, "upper_bound": None, "delta_hat": None})
        b = stats.cp_union(3, 3, 20, "0.05")                  # a tie
        self.assertLess(b["lower_bound"], 0)
        self.assertEqual(b["delta_hat"], 0)
        b = stats.cp_union(30, 0, 40, "0.05")
        self.assertGreater(b["lower_bound"], 0)
        self.assertEqual(stats.cp_lower(30, 40, Fraction(1, 40)) - stats.cp_upper(0, 40,
                                                                                  Fraction(1, 40)),
                         b["lower_bound"])
        with self.assertRaises(ValueError):
            stats.cp_union(5, 6, 10, "0.05")

    def test_paired_counts(self):
        c = stats.paired_counts([(0, 1), (1, 0), (1, 1), (0, 0), (0, 1)])
        self.assertEqual((c["n"], c["w"], c["l"], c["both_solved"], c["both_failed"],
                          c["incumbent_successes"], c["candidate_successes"]),
                         (5, 2, 1, 1, 1, 2, 3))


NB_SAME = {"incumbent_bytes": 300, "incumbent_tokens": 100, "candidate_bytes": 300,
           "candidate_tokens": 100, "cap_tokens": 100,
           "tokenizer": {"kind": "proxy-bytes-div-3", "version": "1"}}


def counts(w, l, n, both=0):
    return {"n": n, "w": w, "l": l, "both_solved": both, "both_failed": n - w - l - both,
            "incumbent_successes": l + both, "candidate_successes": w + both}


class Verdicts(unittest.TestCase):
    """L24/L25: verdict rules of spec 8.6."""

    def v(self, stage, c, nb=NB_SAME, complete=True, planned=None, provisional=False, pol=None):
        return DE.comparison_verdict(stage, c, planned or c["n"], complete, nb,
                                     pol or policy(), "family_disjoint", provisional)[:2]

    def test_performance_longer_note(self):
        longer = dict(NB_SAME, incumbent_tokens=50, incumbent_bytes=150)
        self.assertEqual(self.v("confirm", counts(30, 0, 40), longer)[0], "pass_performance")

    def test_tie_longer_never_promoted(self):
        longer = dict(NB_SAME, incumbent_tokens=50, incumbent_bytes=150)
        for c in (counts(0, 0, 100), counts(5, 5, 20), counts(40, 38, 100)):
            self.assertIn(self.v("confirm", c, longer)[0], ("inconclusive", "fail"))
            self.assertIn(self.v("confirm", c)[0], ("inconclusive", "fail"))  # equal length
        self.assertEqual(self.v("confirm", counts(0, 30, 40), longer)[0], "fail")

    def test_compression(self):
        shorter = dict(NB_SAME, candidate_tokens=50, candidate_bytes=150)
        self.assertEqual(self.v("confirm", counts(0, 0, 400), shorter)[0], "pass_compression")
        self.assertEqual(self.v("confirm", counts(0, 0, 20), shorter)[0], "inconclusive")
        self.assertEqual(self.v("confirm", counts(0, 30, 40), shorter)[0], "fail")

    def test_all_failures_and_n0(self):
        self.assertEqual(self.v("confirm", counts(0, 0, 20))[0], "inconclusive")
        self.assertEqual(self.v("confirm", counts(0, 20, 20))[0], "fail")
        self.assertEqual(self.v("confirm", counts(0, 0, 0), planned=20)[0], "infra_error")

    def test_incomplete_not_promotable(self):
        self.assertEqual(self.v("confirm", counts(30, 0, 40), complete=False)[0], "infra_error")
        self.assertEqual(self.v("confirm", counts(30, 0, 40), planned=100)[0], "infra_error")

    def test_cap(self):
        over = dict(NB_SAME, candidate_tokens=101)
        self.assertEqual(self.v("confirm", counts(30, 0, 40), over)[0], "fail")

    def test_screen_gate(self):
        self.assertEqual(self.v("screen", counts(1, 0, 6)),
                         ("inconclusive", "screen_promising: continue to an independent "
                                          "confirmation"))
        self.assertEqual(self.v("screen", counts(0, 0, 6))[0], "fail")
        shorter = dict(NB_SAME, candidate_tokens=50, candidate_bytes=150)
        self.assertEqual(self.v("screen", counts(0, 0, 6), shorter)[0], "inconclusive")
        self.assertEqual(self.v("screen", counts(0, 1, 6), shorter)[0], "fail")   # -1/6 < -0.05

    def test_provisional_requires_policy(self):
        self.assertEqual(self.v("confirm", counts(30, 0, 40), provisional=True)[0],
                         "inconclusive")
        p = policy()
        p["promotion"]["provisional_within_family"] = True
        self.assertEqual(self.v("confirm", counts(30, 0, 40), provisional=True, pol=p)[0],
                         "pass_performance")

    def test_confirm_scope(self):
        p = policy()
        self.assertEqual(DE.confirm_scope(p, "design", True), ("family_disjoint", False))
        # three independent design families and none reserved with eligible arms: required
        self.assertIn("must reserve", DE.confirm_scope(p, "design", False))
        p = policy(families=[family("fam-a"), family("fam-b")])
        self.assertIn("does not authorize", DE.confirm_scope(p, "design", False))
        p["promotion"]["provisional_within_family"] = True
        self.assertEqual(DE.confirm_scope(p, "design", False), ("fresh_seed", True))


class Sampling(unittest.TestCase):
    def test_seed_bits_masking(self):
        rng = sampling.RandomSource(lambda n: b"\xff" * n)
        self.assertEqual(rng.seed_bits(3), "111")
        rng = sampling.RandomSource(lambda n: bytes([0b00000101, 0b1]))
        self.assertEqual(rng.seed_bits(9), "101000001")

    def test_uniform_rejection(self):
        stream = iter([7, 6, 5, 2])                # 3 bits for n = 5: 7, 6, 5 rejected
        rng = sampling.RandomSource(lambda n: bytes([next(stream)]))
        self.assertEqual(rng.uniform(5), 2)

    def test_categorical_exact(self):
        """Every accepted byte maps without modulo bias: weights [1, 2] use 2 bits, value 3 is
        rejected (and then the next byte is read)."""
        hits = Counter()
        for v in range(256):
            if v & 3 == 3:
                continue
            rng = sampling.RandomSource(lambda n, v=v: bytes([v]))
            hits[rng.categorical([1, 2])] += 1
        self.assertEqual(hits[1], 2 * hits[0])
        stream = iter([3, 7, 1])
        rng = sampling.RandomSource(lambda n: bytes([next(stream)]))
        self.assertEqual(rng.categorical([1, 2]), 1)

    def test_commitments(self):
        rng = sampling.RandomSource()
        d = sampling.draw_seed(rng, 20, "ctx")
        self.assertEqual(len(d["seed_bits"]), 20)
        self.assertTrue(sampling.verify_reveal("ctx", d))
        self.assertFalse(sampling.verify_reveal("other", d))
        self.assertNotEqual(sampling.draw_seed(rng, 20, "ctx")["seed_commitment"],
                            d["seed_commitment"])
        self.assertIn(sampling.run_order(d["seed_commitment"]),
                      (("incumbent", "candidate"), ("candidate", "incumbent")))


def gen(fid, gid, version=1, levels=3):
    return {"family_id": fid, "generator_id": gid, "version": version, "levels": levels}


def arm(n, s, stale=False):
    return {"n": n, "successes": s, "stale": stale, "p_hat": s / n if n else None,
            "ci": None, "record_ids": []}


class Curriculum(unittest.TestCase):
    """L22, L23."""

    def test_nearest_target_no_monotonicity(self):
        g = gen("fam-a", "g1")
        arms = {("fam-a", "g1", 1, 0): arm(20, 2), ("fam-a", "g1", 1, 1): arm(20, 18),
                ("fam-a", "g1", 1, 2): arm(20, 9)}
        s = CU.select([g], arms, policy())[0]
        self.assertEqual((s["level"], s["eligibility"]), (2, "eligible"))

    def test_tie_break_lower_level(self):
        g = gen("fam-a", "g1")
        arms = {("fam-a", "g1", 1, 2): arm(20, 6), ("fam-a", "g1", 1, 1): arm(20, 10)}
        self.assertEqual(CU.select([g], arms, policy())[0]["level"], 1)   # |0.3-0.4|=|0.5-0.4|

    def test_low_priority_uncalibrated_stale(self):
        g = gen("fam-a", "g1", levels=1)
        self.assertEqual(CU.select([g], {("fam-a", "g1", 1, 0): arm(20, 19)}, policy())[0]
                         ["eligibility"], "low_priority")
        self.assertEqual(CU.select([g], {("fam-a", "g1", 1, 0): arm(3, 1)}, policy())[0]
                         ["eligibility"], "uncalibrated")
        self.assertEqual(CU.select([g], {("fam-a", "g1", 1, 0): arm(20, 8, stale=True)},
                                   policy())[0]["eligibility"], "uncalibrated")
        self.assertEqual(CU.select([g], {}, policy())[0]["eligibility"], "uncalibrated")

    def test_aggregate_and_stale(self):
        p = policy()
        base = {"role": "design", "profile_id": "profile-0001",
                "reference_notebook_sha256": "sha256:" + "0" * 64, "contract_id": "c",
                "failures": {"invalid_proof": 1}, "infra_errors": 1, "record_id": "r"}
        recs = [dict(base, family_id="fam-a", generator_id="g", version=1, level=0, n=10,
                     successes=4, created_at="2027-01-15T08:00:00Z"),
                dict(base, family_id="fam-a", generator_id="g", version=1, level=0, n=10,
                     successes=5, created_at="2027-01-15T08:00:00Z"),
                dict(base, family_id="fam-a", generator_id="g", version=1, level=0, n=10,
                     successes=5, created_at="2027-01-15T08:00:00Z",
                     profile_id="other")]
        a = CU.aggregate(recs, "design", "profile-0001", "sha256:" + "0" * 64, 30, T0)
        k = ("fam-a", "g", 1, 0)
        self.assertEqual((a[k]["n"], a[k]["successes"], a[k]["infra_errors"]), (20, 9, 2))
        self.assertFalse(a[k]["stale"])
        a = CU.aggregate(recs, "design", "profile-0001", "sha256:" + "0" * 64, 30,
                         T0 + 40 * 86400)
        self.assertTrue(a[k]["stale"])

    def test_family_balanced_mixture(self):
        p = policy()
        sel = [dict(gen("fam-a", "a1"), level=0, eligibility="eligible"),
               dict(gen("fam-a", "a2"), level=1, eligibility="eligible"),
               dict(gen("fam-b", "b1"), level=0, eligibility="eligible")]
        m = CU.freeze_mixture(sel, p, {"fam-a", "fam-b"})
        w = {x["generator_id"]: Fraction(*x["weight"]) for x in m["mixture"]}
        self.assertEqual(w, {"a1": Fraction(1, 4), "a2": Fraction(1, 4), "b1": Fraction(1, 2)})
        # versions are not counted: the registry gives one (the newest) version per generator,
        # so adding versions of b1 cannot change anything; a near-duplicate *generator* only
        # splits its own family's half.
        sel.append(dict(gen("fam-b", "b2"), level=0, eligibility="eligible"))
        w = {x["generator_id"]: Fraction(*x["weight"])
             for x in CU.freeze_mixture(sel, p, {"fam-a", "fam-b"})["mixture"]}
        self.assertEqual(w["a1"] + w["a2"], Fraction(1, 2))
        self.assertEqual(CU.integer_weights(CU.freeze_mixture(sel, p, {"fam-a", "fam-b"})
                                            ["mixture"]), [1, 1, 1, 1])

    def test_group_weighting(self):
        p = policy(families=[family("fam-a", group="g"), family("fam-b", group="g"),
                             family("fam-x")])
        sel = [dict(gen(f, f + "1"), level=0, eligibility="eligible")
               for f in ("fam-a", "fam-b", "fam-x")]
        w = {x["family_id"]: Fraction(*x["weight"])
             for x in CU.freeze_mixture(sel, p, {"fam-a", "fam-b", "fam-x"})["mixture"]}
        self.assertEqual(w, {"fam-a": Fraction(1, 4), "fam-b": Fraction(1, 4),
                             "fam-x": Fraction(1, 2)})

    def test_insufficient(self):
        sel = [dict(gen("fam-a", "a1"), level=0, eligibility="low_priority")]
        m = CU.freeze_mixture(sel, policy(), {"fam-a"})
        self.assertEqual(m["status"], "insufficient_generators")
        self.assertEqual(len(m["exploration"]), 1)

    def test_due_arms(self):
        g = gen("fam-a", "g1", levels=3)
        arms = {("fam-a", "g1", 1, 0): arm(4, 1), ("fam-a", "g1", 1, 1): arm(2, 1),
                ("fam-a", "g1", 1, 2): arm(4, 2, stale=True)}
        due = CU.due_arms([g], arms, policy())
        self.assertEqual([(d["level"], d["trials"]) for d in due], [(2, 4), (1, 2)])


if __name__ == "__main__":
    unittest.main()
