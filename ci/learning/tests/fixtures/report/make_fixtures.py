"""Regenerate the SYNTHETIC report fixtures in this directory.

Every value here is invented for testing the report generator. None of it is an observed
measurement, and none of it may be published as a real metric.

    python3 ci/learning/tests/fixtures/report/make_fixtures.py
"""

import hashlib
import json
import math
import os

HERE = os.path.dirname(os.path.abspath(__file__))
CORE = "c" * 40
DAG = "d" * 40
ENV = "env-synthetic"


def canonical(obj):
    return json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=False).encode()


def digest(obj):
    return "sha256:" + hashlib.sha256(canonical(obj)).hexdigest()


def h(label):
    return "sha256:" + hashlib.sha256(("synthetic:" + label).encode()).hexdigest()


def make(kind, created_at, **fields):
    rec = {"schema": "sigaba.learning.%s.v1" % kind, "core_revision": CORE, "dag_snapshot": DAG,
           "environment_id": ENV}
    rec.update(fields)
    rec["record_id"] = digest(rec)
    if kind == "contract":
        rec["contract_id"] = rec["record_id"]
    rec["created_at"] = created_at
    return rec


def wilson(s, n, z=1.959963984540054):
    p = s / n
    d = 1 + z * z / n
    c = p + z * z / (2 * n)
    r = z * math.sqrt(p * (1 - p) / n + z * z / (4 * n * n))
    return max(0.0, (c - r) / d), min(1.0, (c + r) / d)


class Store:
    def __init__(self):
        self.files = {k: [] for k in ("certifications", "calibrations", "contracts", "trials",
                                      "comparisons", "activations")}

    def add(self, kind, rec):
        self.files[kind].append(rec)
        return rec

    def write(self, name):
        d = os.path.join(HERE, name)
        os.makedirs(d, exist_ok=True)
        for kind, recs in self.files.items():
            if not recs:
                continue
            with open(os.path.join(d, kind + ".jsonl"), "w", encoding="utf-8") as fh:
                for r in recs:
                    fh.write(canonical(r).decode() + "\n")


USAGE = {"model_calls": 3, "input_tokens": 1000, "output_tokens": 200, "reasoning_tokens": None,
         "cached_tokens": None, "wall_seconds": 60, "lean_seconds": 10}


def cert(st, role, date, fam, gen, ver, status, k=16, hb=16, req=16, equiv="Same", rev="r1",
         refs=("theorem:synthetic-a",), reason="ok", **extra):
    rec = dict(role=role, family_id=fam, family_revision=h("rev-" + rev), generator_id=gen,
               version=ver, path="generators/%s/%s/%s/v%04d" % (role, fam, gen, ver), pr=100 + ver,
               head="a" * 40, author="synthetic-author", files={}, seed_bits=k, levels=3,
               entropy_bits=hb, required_bits=req,
               equivalence="SigabaNeo.Benchmark.Families.Synthetic." + equiv,
               certificate_decl="Synthetic.%s.cert" % gen, generate_decl="Synthetic.%s.gen" % gen,
               lean_result={"verdict": "ACCEPTED" if status != "rejected" else "REJECTED",
                            "problems": []},
               smoke=[], status=status, reason=reason,
               source_refs=[{"node_id": r, "commit": "e" * 40, "content_sha256": h(r)}
                            for r in refs], bootstrap=False)
    rec.update(extra)
    return st.add("certifications", make("certification", date + "T09:00:00Z", **rec))


def profile(pid, model):
    return {"profile_id": pid, "provider": "mock", "model": model, "settings": {},
            "budget": {"max_model_calls": 50, "max_input_tokens": 400000,
                       "max_output_tokens": 100000, "wall_seconds": 3600, "lean_seconds": 1800}}


def contract(st, role, date, stage, scope, arms, mixture, profile_obj, epoch="epoch-0001",
             provisional=False, trials_planned=20):
    return st.add("contracts", make(
        "contract", date + "T08:00:00Z", stage=stage, role=role, scope=scope,
        provisional=provisional,
        arms=[{"arm": a, "notebook_sha256": nb, "notebook_bytes": b, "notebook_tokens": t,
               "pr": None, "head": None} for a, nb, b, t in arms],
        mixture=mixture, excluded_families=[], trials_planned=trials_planned,
        profile=profile_obj, policy_id="policy-synthetic", policy_sha256=h("policy"),
        epoch_id=epoch, calibration_snapshot=[],
        rng={"source": "os.urandom", "algorithm": "sigaba-learning-sample-v1"},
        seed_commitment_scheme="sha256(domain || salt || seed)",
        verifier={"core_revision": CORE, "environment_id": ENV}, score_rule="binary-v1",
        statistics={"method": "cp-union-v1", "alpha": 0.05, "delta_ni": 0.05}))


def trial(st, c, date, stage, pair_id, arm, nb, mix, outcome, reason, retries=0, idx=None):
    return st.add("trials", make(
        "trial", date + "T07:00:00Z", run_id="run-" + c["contract_id"][7:15],
        contract_id=c["contract_id"], stage=stage, pair_id=pair_id, arm=arm, role=c["role"],
        family_id=mix["family_id"], generator_id=mix["generator_id"], version=mix["version"],
        level=mix["level"],
        seed_commitment=h("seed-%s-%s-%s-%s-%s-%s" % (c["contract_id"], pair_id, arm, retries,
                                                       mix["level"], idx)),
        descriptor_sha256=h("desc-%s-%s-%s-%s" % (c["contract_id"], pair_id, mix["level"], idx)), notebook_sha256=nb,
        model_reported=c["profile"]["model"], started_at=date + "T06:00:00Z",
        ended_at=date + "T06:30:00Z", outcome=outcome, reason=reason,
        check={"verdict": "ACCEPTED", "theorem_sha256": h("thm")} if outcome == "solved"
        else None,
        usage=USAGE, retries=retries, certified_value=None))


def comparison(st, c, date, n, w, l, bs, verdict, reason, lb, inc_nb, cand_nb, sizes,
               anchor_epoch=None, cap=4096, tokenizer="proxy-bytes-div-3 v1", infra=()):
    """Builds the 2n paired trials (outcomes consistent with w, l, bs) and the comparison."""
    mix = c["mixture"]
    stage = c["stage"]
    inc_arm = "anchor_baseline" if stage == "anchor" else "incumbent"
    pairs = []
    for i in range(n):
        if i < w:
            o = ("unsolved", "solved")
        elif i < w + l:
            o = ("solved", "unsolved")
        elif i < w + l + bs:
            o = ("solved", "solved")
        else:
            o = ("unsolved", "unsolved")
        m = mix[i % len(mix)]
        ti = trial(st, c, date, stage, i, inc_arm, inc_nb, m, o[0],
                   "verified" if o[0] == "solved" else "invalid_proof")
        tc = trial(st, c, date, stage, i, "candidate", cand_nb, m, o[1],
                   "verified" if o[1] == "solved" else "budget_exhausted")
        pairs.append([ti["record_id"], tc["record_id"]])
    for pair_id, arm, nb, reason_ in infra:
        trial(st, c, date, stage, pair_id, arm, nb, mix[0], "infra_error", reason_, retries=1,
              idx="infra")
    inc_s, cand_s = bs + l, bs + w
    return st.add("comparisons", make(
        "comparison", date + "T12:00:00Z", role=c["role"], contract_id=c["contract_id"],
        stage=stage, scope=c["scope"], provisional=c["provisional"], incumbent_sha256=inc_nb,
        candidate_sha256=cand_nb, pr=200, head="b" * 40, pair_refs=pairs, n=n,
        incumbent_successes=inc_s, candidate_successes=cand_s, w=w, l=l, both_solved=bs,
        both_failed=n - w - l - bs, delta_hat=((w - l) / n) if n else None, lower_bound=lb,
        method="cp-union-v1", alpha=0.05, delta_ni=0.05,
        notebook={"incumbent_bytes": sizes[0], "incumbent_tokens": sizes[1],
                  "candidate_bytes": sizes[2], "candidate_tokens": sizes[3], "cap_tokens": cap,
                  "tokenizer": tokenizer},
        usage={"incumbent": {"model_calls": 3 * n}, "candidate": {"model_calls": 3 * n}},
        verdict=verdict, reason=reason, policy_id="policy-synthetic", epoch_id=c["epoch_id"],
        anchor_epoch=anchor_epoch))


def calibration(st, c, date, mix, n, s, state, selected, eligibility, ref_nb, profile_id,
                infra=0, gen_error=0):
    trial_ids = []
    for i in range(n):
        t = trial(st, c, date, "calibration", None, "reference", ref_nb,
                  dict(mix, version=mix["version"]), "solved" if i < s else "unsolved",
                  "verified" if i < s else "solver_timeout", idx=i)
        trial_ids.append(t["record_id"])
    for j in range(infra):
        t = trial(st, c, date, "calibration", None, "reference", ref_nb, mix, "infra_error",
                  "provider_error", retries=1, idx=100 + j)
        trial_ids.append(t["record_id"])
    for j in range(gen_error):
        t = trial(st, c, date, "calibration", None, "reference", ref_nb, mix, "infra_error",
                  "generation_error", retries=1, idx=200 + j)
        trial_ids.append(t["record_id"])
    ci = None
    if n:
        lo, hi = wilson(s, n)
        ci = {"method": "wilson-95", "low": lo, "high": hi}
    return st.add("calibrations", make(
        "calibration", date + "T10:00:00Z", role=c["role"], family_id=mix["family_id"],
        generator_id=mix["generator_id"], version=mix["version"], level=mix["level"],
        profile_id=profile_id, reference_notebook_sha256=ref_nb, contract_id=c["contract_id"],
        trial_ids=trial_ids, n=n, successes=s,
        failures={"solver_timeout": n - s} if n else {}, infra_errors=infra + gen_error,
        p_hat=(s / n) if n else None, ci=ci, usage={"model_calls": 3 * n}, state=state,
        selected=selected, eligibility=eligibility))


def activation(st, role, date, seq, pred, succ, reason, scope, provisional, cmps, actor="maint"):
    return st.add("activations", make(
        "activation", date + "T15:00:00Z", role=role, predecessor_sha256=pred,
        successor_sha256=succ, pr=300 + seq, head="f" * 40, merge_commit="9" * 40,
        comparison_ids=[c["record_id"] for c in cmps], scope=scope, provisional=provisional,
        reason=reason, actor=actor, policy_id="policy-synthetic", epoch_id="epoch-0001",
        anchor_refs=[], sequence=seq))


def mixentry(fam, gen, ver, level, num, den):
    return {"family_id": fam, "generator_id": gen, "version": ver, "level": level,
            "weight": [num, den]}


def build_rich():
    st = Store()
    D = "design"
    # --- Design: certifications (multiple versions, quarantine, supersession, rejection,
    # equivalence change).
    cert(st, D, "2026-10-01", "avoid-word", "aw-basic", 1, "certified",
         refs=("theorem:synthetic-a", "theorem:synthetic-b"))
    cert(st, D, "2026-10-05", "sum-fam", "sum-bad", 1, "rejected", reason="certificate failed")
    cert(st, D, "2026-10-10", "avoid-word", "aw-basic", 2, "certified", k=20, hb=18,
         refs=("theorem:synthetic-a", "definition:synthetic-c"))
    cert(st, D, "2026-10-12", "avoid-word", "aw-alt", 1, "certified",
         refs=("theorem:synthetic-d",))
    cert(st, D, "2026-10-15", "sum-fam", "sum-gen", 1, "certified", k=24, hb=20, req=20,
         refs=("solution:synthetic-e",))
    cert(st, D, "2026-10-20", "avoid-word", "aw-alt", 1, "quarantined",
         reason="smoke test failure")
    cert(st, D, "2026-10-25", "avoid-word", "aw-basic", 3, "certified", k=20, hb=19,
         equiv="SameV2", rev="r2", refs=("theorem:synthetic-a",))
    cert(st, D, "2026-10-25", "avoid-word", "aw-basic", 1, "superseded", reason="replaced")

    p1 = profile("profile-0001", "mock-1")
    p2 = profile("profile-0002", "mock-2")
    N = {k: h("design-notebook-" + k) for k in ("E", "0", "1", "2", "3", "4", "5")}
    aw2 = {"family_id": "avoid-word", "generator_id": "aw-basic", "version": 2}
    sg1 = {"family_id": "sum-fam", "generator_id": "sum-gen", "version": 1}
    # --- Calibrations (stale, n = 0, model change, infra and generation errors).
    cal = contract(st, D, "2026-10-11", "calibration", "fresh_seed",
                   [("reference", N["0"], 1200, 400)],
                   [mixentry("avoid-word", "aw-basic", 2, 1, 1, 3),
                    mixentry("avoid-word", "aw-basic", 2, 2, 1, 3),
                    mixentry("sum-fam", "sum-gen", 1, 1, 1, 3)], p1, trials_planned=60)
    calibration(st, cal, "2026-10-11", dict(aw2, level=1), 20, 8, "fresh", True, "eligible",
                N["0"], "profile-0001", infra=1)
    calibration(st, cal, "2026-10-11", dict(aw2, level=2), 20, 2, "fresh", False,
                "low_priority", N["0"], "profile-0001")
    calibration(st, cal, "2026-10-11", dict(aw2, level=3), 0, 0, "fresh", False,
                "uncalibrated", N["0"], "profile-0001")
    calibration(st, cal, "2026-10-16", dict(sg1, level=1), 20, 10, "fresh", True, "eligible",
                N["0"], "profile-0001", gen_error=1)
    cal_b = contract(st, D, "2026-11-05", "calibration", "fresh_seed",
                     [("reference", N["1"], 1500, 500)],
                     [mixentry("avoid-word", "aw-basic", 2, 1, 1, 1)], p1, trials_planned=20)
    calibration(st, cal_b, "2026-11-05", dict(aw2, level=1), 20, 9, "stale", True, "eligible",
                N["0"], "profile-0001")
    cal2 = contract(st, D, "2026-11-10", "calibration", "fresh_seed",
                    [("reference", N["1"], 1500, 500)],
                    [mixentry("avoid-word", "aw-basic", 2, 1, 1, 1)], p2, epoch="epoch-0002",
                    trials_planned=20)
    calibration(st, cal2, "2026-11-10", dict(aw2, level=1), 20, 12, "fresh", True, "eligible",
                N["1"], "profile-0002")

    train = [mixentry("avoid-word", "aw-basic", 2, 1, 1, 2),
             mixentry("sum-fam", "sum-gen", 1, 1, 1, 2)]
    disjoint = [mixentry("sum-fam", "sum-gen", 1, 1, 1, 1)]
    anchor_mix = [mixentry("avoid-word", "aw-basic", 2, 1, 1, 1)]

    activation(st, D, "2026-10-02", 1, None, N["0"], "bootstrap", None, False, [])
    s1 = contract(st, D, "2026-10-18", "screen", "fresh_seed",
                  [("incumbent", N["0"], 1200, 400), ("candidate", N["1"], 1500, 500)], train, p1)
    cs1 = comparison(st, s1, "2026-10-18", 20, 6, 2, 4, "pass_performance", "screen promising",
                     -0.21, N["0"], N["1"], (1200, 400, 1500, 500),
                     infra=((3, "candidate", N["1"], "provider_error"),))
    c1 = contract(st, D, "2026-10-19", "confirm", "fresh_seed",
                  [("incumbent", N["0"], 1200, 400), ("candidate", N["1"], 1500, 500)], train, p1,
                  provisional=True, trials_planned=30)
    cc1 = comparison(st, c1, "2026-10-20", 30, 10, 2, 6, "pass_performance",
                     "lower bound above zero", 0.02, N["0"], N["1"], (1200, 400, 1500, 500))
    activation(st, D, "2026-10-21", 2, N["0"], N["1"], "improvement", "fresh_seed", True, [cc1])
    a1 = contract(st, D, "2026-10-22", "anchor", "fresh_seed",
                  [("anchor_baseline", N["E"], 0, 0), ("incumbent", N["1"], 1500, 500)],
                  anchor_mix, p1)
    comparison(st, a1, "2026-10-22", 20, 6, 1, 4, "inconclusive", "anchor panel", -0.02, N["E"],
               N["1"], (0, 0, 1500, 500), anchor_epoch="anchor-0001")
    s2 = contract(st, D, "2026-10-26", "screen", "fresh_seed",
                  [("incumbent", N["1"], 1500, 500), ("candidate", N["2"], 900, 300)], train, p1)
    comparison(st, s2, "2026-10-26", 20, 3, 3, 7, "pass_compression", "screen promising", -0.25,
               N["1"], N["2"], (1500, 500, 900, 300))
    c2 = contract(st, D, "2026-10-27", "confirm", "family_disjoint",
                  [("incumbent", N["1"], 1500, 500), ("candidate", N["2"], 900, 300)], disjoint,
                  p1, trials_planned=30)
    cc2 = comparison(st, c2, "2026-10-28", 30, 4, 5, 12, "pass_compression",
                     "shorter and non-inferior", -0.045, N["1"], N["2"], (1500, 500, 900, 300))
    activation(st, D, "2026-10-29", 3, N["1"], N["2"], "compression", "family_disjoint", False,
               [cc2])
    a2 = contract(st, D, "2026-10-30", "anchor", "fresh_seed",
                  [("anchor_baseline", N["E"], 0, 0), ("incumbent", N["2"], 900, 300)],
                  anchor_mix, p1)
    comparison(st, a2, "2026-10-30", 20, 8, 1, 5, "pass_performance", "anchor panel", 0.05,
               N["E"], N["2"], (0, 0, 900, 300), anchor_epoch="anchor-0001")
    s3 = contract(st, D, "2026-11-01", "screen", "fresh_seed",
                  [("incumbent", N["2"], 900, 300), ("candidate", N["3"], 2000, 700)], train, p1)
    comparison(st, s3, "2026-11-01", 20, 1, 5, 4, "fail", "no improvement", -0.55, N["2"],
               N["3"], (900, 300, 2000, 700))
    c4 = contract(st, D, "2026-11-02", "confirm", "fresh_seed",
                  [("incumbent", N["2"], 900, 300), ("candidate", N["4"], 800, 260)], train, p1,
                  trials_planned=30)
    comparison(st, c4, "2026-11-03", 30, 6, 4, 8, "inconclusive", "interval spans margin",
               -0.14, N["2"], N["4"], (900, 300, 800, 260))
    activation(st, D, "2026-11-06", 4, N["2"], N["1"], "rollback", "fresh_seed", False, [],
               actor="maintainer-rollback")
    s5 = contract(st, D, "2026-11-08", "screen", "fresh_seed",
                  [("incumbent", N["1"], 1500, 500), ("candidate", N["5"], 1400, 470)], train, p1)
    comparison(st, s5, "2026-11-08", 0, 0, 0, 0, "awaiting_evaluator", "no evaluator", None,
               N["1"], N["5"], (1500, 500, 1400, 470))
    # Compare-and-swap violation: predecessor is not the active notebook.
    activation(st, D, "2026-11-09", 5, N["0"], N["4"], "improvement", "fresh_seed", False, [])
    a3 = contract(st, D, "2026-11-12", "anchor", "fresh_seed",
                  [("anchor_baseline", N["E"], 0, 0), ("incumbent", N["1"], 1500, 500)],
                  anchor_mix, p2, epoch="epoch-0002")
    comparison(st, a3, "2026-11-12", 20, 5, 1, 8, "pass_performance", "anchor panel", 0.01,
               N["E"], N["1"], (0, 0, 1500, 500), anchor_epoch="anchor-0002")
    # Same anchor epoch label but a different profile: must not join the anchor-0001 series.
    a4 = contract(st, D, "2026-11-13", "anchor", "fresh_seed",
                  [("anchor_baseline", N["E"], 0, 0), ("incumbent", N["1"], 1500, 500)],
                  anchor_mix, p2)
    comparison(st, a4, "2026-11-13", 20, 4, 2, 6, "inconclusive", "anchor panel", -0.2, N["E"],
               N["1"], (0, 0, 1500, 500), anchor_epoch="anchor-0001")

    # --- Cryptanalysis: one active notebook, missing tokenizer, infrastructure failure.
    C = "cryptanalysis"
    pc = profile("profile-c1", "mock-1")
    M = {k: h("crypt-notebook-" + k) for k in ("0", "1")}
    la = {"family_id": "lin-attack", "generator_id": "la-1", "version": 1}
    cert(st, C, "2026-10-03", "lin-attack", "la-1", 1, "certified", k=32, hb=24, req=24,
         refs=("theorem:synthetic-x",))
    calc = contract(st, C, "2026-10-04", "calibration", "fresh_seed",
                    [("reference", M["0"], 2048, None)],
                    [mixentry("lin-attack", "la-1", 1, 1, 1, 1)], pc)
    calibration(st, calc, "2026-10-04", dict(la, level=1), 20, 7, "fresh", True, "eligible",
                M["0"], "profile-c1")
    activation(st, C, "2026-10-05", 1, None, M["0"], "bootstrap", None, False, [])
    cs = contract(st, C, "2026-10-07", "screen", "fresh_seed",
                  [("incumbent", M["0"], 2048, None), ("candidate", M["1"], 1800, None)],
                  [mixentry("lin-attack", "la-1", 1, 1, 1, 1)], pc)
    comparison(st, cs, "2026-10-08", 12, 2, 1, 3, "infra_error",
               "verification infrastructure unavailable", None, M["0"], M["1"],
               (2048, None, 1800, None), tokenizer=None,
               infra=((12, "incumbent", M["0"], "verification_infra_error"),
                      (12, "candidate", M["1"], "verification_infra_error")))
    st.write("rich")


def build_hostile():
    st = Store()
    D = "design"
    cert(st, D, "2026-10-01", 'fam"><svg onload=alert(1)>', '<script>alert("g")</script>', 1,
         "certified", equiv='</script><script>alert(3)</script>',
         reason='=HYPERLINK("evil")', author="[x](javascript:alert(1))",
         refs=("theorem:<b>bold</b>",))
    p = profile('<img src=x onerror=alert(2)>', "mock-</script>")
    nb = h("hostile-notebook")
    c = contract(st, D, "2026-10-02", "calibration", "fresh_seed", [("reference", nb, 10, 3)],
                 [mixentry('fam"><svg onload=alert(1)>', '<script>alert("g")</script>', 1, 1,
                           1, 1)], p)
    calibration(st, c, "2026-10-02",
                {"family_id": 'fam"><svg onload=alert(1)>',
                 "generator_id": '<script>alert("g")</script>', "version": 1, "level": 1},
                4, 1, "fresh", True, "eligible", nb, '<img src=x onerror=alert(2)>')
    s = contract(st, D, "2026-10-03", "screen", "fresh_seed",
                 [("incumbent", nb, 10, 3), ("candidate", h("hostile-2"), 12, 4)],
                 [mixentry("f", "g", 1, 1, 1, 1)], p)
    comparison(st, s, "2026-10-03", 4, 1, 0, 1, "fail", "</script><b>bold</b> | -1+1",
               -0.5, nb, h("hostile-2"), (10, 3, 12, 4))
    activation(st, D, "2026-10-02", 1, None, nb, "bootstrap", "@SUM(A1)", False, [],
               actor="-2+3")
    st.write("hostile")


def build_malformed():
    d = os.path.join(HERE, "malformed")
    os.makedirs(d, exist_ok=True)
    st = Store()
    good = cert(st, "design", "2026-10-01", "fam", "gen", 1, "certified")
    bad_schema = dict(good, schema="sigaba.learning.other.v1", record_id=h("x"))
    no_id = {k: v for k, v in good.items() if k != "record_id"}
    bad_role = dict(good, role="attacker", record_id=h("y"))
    lines = ["{not json", "[1, 2, 3]", json.dumps(no_id, sort_keys=True),
             json.dumps(bad_schema, sort_keys=True), canonical(good).decode(),
             canonical(good).decode(), '{"record_id": "sha256:1", "value": NaN}',
             json.dumps(bad_role, sort_keys=True), ""]
    with open(os.path.join(d, "certifications.jsonl"), "w", encoding="utf-8") as fh:
        fh.write("\n".join(lines) + "\n")
    bad_time = make("trial", "yesterday", role="design", contract_id="sha256:none")
    with open(os.path.join(d, "trials.jsonl"), "w", encoding="utf-8") as fh:
        fh.write(canonical(bad_time).decode() + "\n")


def build_empty():
    d = os.path.join(HERE, "empty")
    os.makedirs(d, exist_ok=True)
    open(os.path.join(d, "certifications.jsonl"), "w").close()


POLICY = {
    "schema": "sigaba.learning.policy.v1", "policy_id": "policy-synthetic",
    "epoch": {"id": "epoch-0001", "dag_snapshot": DAG, "environment_id": ENV,
              "core_revision": CORE, "strength_digest": h("strength")},
    "families": [{"family_id": "avoid-word", "role": "design", "entropy_bits": 16},
                 {"family_id": "sum-fam", "role": "design", "entropy_bits": 20},
                 {"family_id": "lin-attack", "role": "cryptanalysis", "entropy_bits": 24}],
    "notebooks": {"max_tokens": 4096, "max_bytes": 32768,
                  "tokenizer": {"kind": "proxy-bytes-div-3", "version": "1"}},
    "curriculum": {"target": "0.40", "lo": "0.20", "hi": "0.60", "min_samples": 20,
                   "exploration_fraction": "0.10", "stale_after_days": 30},
}


if __name__ == "__main__":
    build_rich()
    build_hostile()
    build_malformed()
    build_empty()
    with open(os.path.join(HERE, "policy.json"), "w", encoding="utf-8") as fh:
        json.dump(POLICY, fh, indent=2, sort_keys=True)
        fh.write("\n")
