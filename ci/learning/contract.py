"""Evaluation contracts (`sigaba.learning.contract.v1`, spec section 8.1).

A contract is frozen before any seed is drawn: role, stage, evidence scope, both arms' exact
notebook bytes (by hash and size), the mixture with exact weights, the excluded families, the
planned number of trials, the full profile, the policy (id and digest), the epoch, the calibration
snapshot, the RNG and commitment scheme, the verifier, the score rule and the statistics. Its
`contract_id` is the digest of all of that (no result field, no timestamp), so the same frozen
inputs give the same id and any change gives a new one.
"""

from __future__ import annotations

from . import policy as POL, records, sampling, stats

STAGES = ("calibration", "screen", "confirm", "anchor", "transfer")


def common(pol: dict, dag_snapshot: str | None = None) -> dict:
    e = pol["epoch"]
    return {"core_revision": e["core_revision"], "dag_snapshot": dag_snapshot or e["dag_snapshot"],
            "environment_id": e["environment_id"]}


def arm(name: str, measure: dict, pr: int | None = None, head: str | None = None) -> dict:
    return {"arm": name, "notebook_sha256": measure["sha256"], "notebook_bytes": measure["bytes"],
            "notebook_tokens": measure["tokens"], "pr": pr, "head": head}


def build(*, stage: str, role: str, scope: str, provisional: bool, arms: list[dict],
          mixture: list[dict], excluded_families: list[str], trials_planned: int, profile: dict,
          pol: dict, calibration_snapshot: list[str]) -> dict:
    if stage not in STAGES:
        raise ValueError(f"unknown stage {stage}")
    pr = pol["promotion"]
    return {"schema": "sigaba.learning.contract.v1", "stage": stage, "role": role,
            "scope": scope, "provisional": provisional, "arms": arms, "mixture": mixture,
            "excluded_families": sorted(set(excluded_families)),
            "trials_planned": trials_planned, "profile": profile,
            "policy_id": pol["policy_id"], "policy_sha256": POL.sha256(pol),
            "epoch_id": pol["epoch"]["id"],
            "calibration_snapshot": sorted(set(calibration_snapshot)),
            "rng": {"source": "os.urandom", "algorithm": sampling.ALGORITHM},
            "seed_commitment_scheme": sampling.SCHEME,
            "verifier": {"core_revision": pol["epoch"]["core_revision"],
                         "environment_id": pol["epoch"]["environment_id"]},
            "score_rule": "binary-v1",
            "statistics": {"method": stats.METHOD, "alpha": pr["alpha"],
                           "delta_ni": pr["delta_ni"]}}


def freeze(c: dict, created_at: str, pol: dict, dag_snapshot: str | None = None) -> dict:
    return records.stamp(c, created_at, common(pol, dag_snapshot))
