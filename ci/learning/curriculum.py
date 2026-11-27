"""The automatic curriculum (spec section 7): empirical difficulty, not a formal theorem.

* `aggregate` sums the compatible calibration batches of every arm (generator version x level):
  same role, profile and reference notebook (and, when given, contracts of the same epoch). An arm
  whose newest batch is older than `stale_after_days` is `stale`. `n` counts complete trials only;
  infrastructure errors are reported apart and never count as failures. `n = 0` is
  `uncalibrated`, never 0%.
* `select` picks, for each generator, the level whose success estimate is nearest the target
  (0.40) among adequately sampled (`n >= min_samples`), fresh arms, with ties broken by the lower
  level number (a stable order). Levels are never assumed monotone in difficulty. The chosen level
  is `eligible` when its estimate is in [lo, hi], otherwise `low_priority` (kept for exploration,
  never passed off as a suitable level). A generator with no adequately sampled level is
  `uncalibrated`.
* `freeze_mixture` builds the family-balanced mixture over eligible arms: equal weight per
  maintainer `group` of families, then per family within the group, then per generator within
  the family (one version per generator: the newest usable one), as exact integer fractions. More
  versions of a generator never add weight. No eligible arm gives `insufficient_generators`.
* `due_arms` lists the arms calibration should sample next (uncalibrated, stale, then
  under-sampled), in a deterministic round-robin order.
"""

from __future__ import annotations

import time
from fractions import Fraction
from math import lcm

from . import canon, policy as POL, stats


def arm_key(r: dict) -> tuple:
    return (r["family_id"], r["generator_id"], r["version"], r["level"])


def aggregate(calibrations: list[dict], role: str, profile_id: str, reference_sha: str,
              stale_after_days: int, as_of: float | None = None,
              contract_ids: set[str] | None = None) -> dict[tuple, dict]:
    as_of = time.time() if as_of is None else as_of
    out: dict[tuple, dict] = {}
    for r in calibrations:
        if r["role"] != role or r["profile_id"] != profile_id or \
                r["reference_notebook_sha256"] != reference_sha:
            continue
        if contract_ids is not None and r["contract_id"] not in contract_ids:
            continue
        a = out.setdefault(arm_key(r), {"n": 0, "successes": 0, "infra_errors": 0,
                                        "failures": {}, "last": 0.0, "record_ids": []})
        a["n"] += r["n"]
        a["successes"] += r["successes"]
        a["infra_errors"] += r["infra_errors"]
        for k, v in r["failures"].items():
            a["failures"][k] = a["failures"].get(k, 0) + v
        a["last"] = max(a["last"], canon.parse_time(r["created_at"]))
        a["record_ids"].append(r["record_id"])
    for a in out.values():
        a["stale"] = as_of - a["last"] > stale_after_days * 86400
        a["p_hat"] = a["successes"] / a["n"] if a["n"] else None
        ci = stats.wilson(a["successes"], a["n"])
        a["ci"] = {"method": "wilson-95", "low": ci[0], "high": ci[1]} if ci else None
    return out


def select(generators: list[dict], arms: dict[tuple, dict], pol: dict) -> list[dict]:
    cur = pol["curriculum"]
    target, lo, hi = POL.prob(cur["target"]), POL.prob(cur["lo"]), POL.prob(cur["hi"])
    out = []
    for g in generators:
        cands = []
        for level in range(g["levels"]):
            a = arms.get((g["family_id"], g["generator_id"], g["version"], level))
            if a and a["n"] >= cur["min_samples"] and not a["stale"]:
                cands.append((abs(Fraction(a["successes"], a["n"]) - target), level, a))
        row = {"family_id": g["family_id"], "generator_id": g["generator_id"],
               "version": g["version"], "level": None, "p_hat": None, "n": 0, "ci": None,
               "eligibility": "uncalibrated"}
        if cands:
            _, level, a = min(cands, key=lambda c: (c[0], c[1]))
            p = Fraction(a["successes"], a["n"])
            row.update(level=level, p_hat=a["p_hat"], n=a["n"], ci=a["ci"],
                       eligibility="eligible" if lo <= p <= hi else "low_priority")
        out.append(row)
    return out


def freeze_mixture(selected: list[dict], pol: dict, families: set[str]) -> dict:
    """The frozen mixture over eligible arms of `families` (exact weights [num, den])."""
    fams = {f["family_id"]: f for f in pol["families"]}
    pool = [s for s in selected if s["eligibility"] == "eligible" and s["family_id"] in families]
    exploration = [s for s in selected if s["eligibility"] != "eligible" and
                   s["family_id"] in families]
    if not pool:
        return {"status": "insufficient_generators", "mixture": [], "exploration": exploration}
    tree: dict[str, dict[str, list[dict]]] = {}
    for s in pool:
        tree.setdefault(fams[s["family_id"]]["group"], {}).setdefault(s["family_id"], []).append(s)
    mixture = []
    for group in sorted(tree):
        for fid in sorted(tree[group]):
            gens = sorted(tree[group][fid], key=lambda s: (s["generator_id"], s["version"]))
            for s in gens:
                w = Fraction(1, len(tree)) / len(tree[group]) / len(gens)
                mixture.append({"family_id": fid, "generator_id": s["generator_id"],
                                "version": s["version"], "level": s["level"],
                                "weight": [w.numerator, w.denominator]})
    assert sum(Fraction(*m["weight"]) for m in mixture) == 1
    return {"status": "ok", "mixture": mixture, "exploration": exploration}


def integer_weights(mixture: list[dict]) -> list[int]:
    """The mixture's weights over a common denominator (for an exact categorical draw)."""
    d = 1
    for m in mixture:
        d = lcm(d, m["weight"][1])
    return [m["weight"][0] * (d // m["weight"][1]) for m in mixture]


def due_arms(generators: list[dict], arms: dict[tuple, dict], pol: dict) -> list[dict]:
    need = pol["curriculum"]["min_samples"]
    rows = []
    for g in generators:
        for level in range(g["levels"]):
            k = (g["family_id"], g["generator_id"], g["version"], level)
            a = arms.get(k)
            if a is None or a["n"] == 0:
                rank, missing = 0, need
            elif a["stale"]:
                rank, missing = 1, need
            elif a["n"] < need:
                rank, missing = 2, need - a["n"]
            else:
                continue
            rows.append({"family_id": k[0], "generator_id": k[1], "version": k[2],
                         "level": level, "rank": rank, "trials": missing})
    return sorted(rows, key=lambda r: (r["rank"], r["family_id"], r["generator_id"],
                                       r["version"], r["level"]))


def families_for(pol: dict, role: str, assessment: tuple[str, ...]) -> set[str]:
    return {f["family_id"] for f in pol["families"]
            if f["role"] == role and f["assessment"] in assessment}
