"""The learning policy, `meta/learning.json` (`sigaba.learning.policy.v1`, maintainers only).

The policy pins the approved task families (their Lean adapters, revisions, seed width `k` and
required entropy `h`), the notebook caps, the curriculum and promotion rules, the evaluation
profiles and whether an evaluator is enabled. A pull request can never change it: `route` rejects
any change outside `dag/`, `generators/` and `notebooks/`.

Probabilities may be written as numbers or decimal strings; `prob` converts them to `Fraction`
through `str`, so that `0.05` means exactly 1/20.
"""

from __future__ import annotations

import json
from fractions import Fraction
from pathlib import Path

from . import canon, notebooks, schema

PATH = "meta/learning.json"
ROLES = ("design", "cryptanalysis")
# A hard ceiling on levels whatever the policy says (the spec suggests eight).
MAX_LEVELS = 64


class PolicyError(Exception):
    pass


def prob(x) -> Fraction:
    return Fraction(str(x))


def problems(p: dict) -> list[str]:
    """Schema problems, then the rules a schema cannot state."""
    probs = schema.check(p, "policy")
    if probs:
        return probs
    seen = set()
    for f in p["families"]:
        fid = f["family_id"]
        if fid in seen:
            probs.append(f"families: {fid} appears twice")
        seen.add(fid)
        # The diversity requirement: 0 < h <= k (h = 0 is no certificate at all).
        if not 0 < f["entropy_bits"] <= f["seed_bits"]:
            probs.append(f"families.{fid}: entropy_bits must satisfy 0 < h <= seed_bits "
                         f"(h={f['entropy_bits']}, k={f['seed_bits']})")
        if f["max_levels"] > MAX_LEVELS:
            probs.append(f"families.{fid}: max_levels above {MAX_LEVELS}")
    fams = {f["family_id"]: f for f in p["families"]}
    for b in p["bootstrap_generators"]:
        f = fams.get(b["family_id"])
        if f is None:
            probs.append(f"bootstrap_generators: unknown family {b['family_id']}")
        elif not f["bootstrap"]:
            probs.append(f"bootstrap_generators: family {b['family_id']} is not a bootstrap family")
    c = p["curriculum"]
    if not prob(c["lo"]) <= prob(c["target"]) <= prob(c["hi"]):
        probs.append("curriculum: need lo <= target <= hi")
    if prob(c["exploration_fraction"]) >= 1:
        probs.append("curriculum: exploration_fraction must be below 1")
    pr = p["promotion"]
    if not 0 < prob(pr["alpha"]) < Fraction(1, 2):
        probs.append("promotion: alpha must be in (0, 1/2)")
    if prob(pr["delta_ni"]) >= 1:
        probs.append("promotion: delta_ni must be below 1")
    if p["notebooks"]["tokenizer"] != notebooks.PROXY:
        probs.append(f"notebooks.tokenizer: only {notebooks.PROXY} is implemented")
    ids = set()
    for pf in p["profiles"]:
        if pf["profile_id"] in ids:
            probs.append(f"profiles: {pf['profile_id']} appears twice")
        ids.add(pf["profile_id"])
    for r in ROLES:
        if sum(1 for pf in p["profiles"] if pf["role"] == r) > 1:
            probs.append(f"profiles: more than one profile for role {r} (the evaluation profile "
                         "of a role must be unambiguous)")
    ev = p["evaluator"]
    if ev["enabled"]:
        if not ev["provider"]:
            probs.append("evaluator: enabled without a provider")
        if ev["max_trials_per_run"] < 1:
            probs.append("evaluator: enabled with max_trials_per_run 0")
        if not any(pf["provider"] == ev["provider"] for pf in p["profiles"]):
            probs.append("evaluator: no profile uses the enabled provider")
    return probs


def load(path: Path) -> dict:
    """The policy at `path`, valid, or `PolicyError`."""
    try:
        p = json.loads(Path(path).read_text())
    except (OSError, json.JSONDecodeError) as e:
        raise PolicyError(f"{path}: {e}") from None
    probs = problems(p)
    if probs:
        raise PolicyError(f"{path}: invalid policy:\n" + "\n".join(probs[:50]))
    return p


def load_base(base: Path) -> dict:
    return load(Path(base) / PATH)


def sha256(p: dict) -> str:
    return canon.digest(p)


def family(p: dict, family_id: str) -> dict | None:
    return next((f for f in p["families"] if f["family_id"] == family_id), None)


def profile(p: dict, role: str) -> dict | None:
    return next((pf for pf in p["profiles"] if pf["role"] == role), None)


def is_bootstrap_generator(p: dict, family_id: str, generator_id: str, version: int) -> bool:
    return {"family_id": family_id, "generator_id": generator_id, "version": version} in \
        p["bootstrap_generators"]


def strength_digest(base: Path) -> str:
    """The digest the epoch pins for the assumption strengths: `sha256:` of the canonical JSON of
    the DAG's `meta/assumptions.json` (or of `null` when it is absent)."""
    p = Path(base) / "meta" / "assumptions.json"
    return canon.digest(json.loads(p.read_text()) if p.exists() else None)
