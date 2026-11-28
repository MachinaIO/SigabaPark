"""The generator registry: derived from immutable records and the files on `main`, never from
agent-asserted metadata.

A version is usable (`certified`) when its latest certification record says `certified`, the files
on `main` have exactly the certified hashes (so a certification of a pull request that was never
merged, or of other bytes, does not count), and it is compatible with the current policy (family
still approved for the role, same family revision, seed width and required entropy). A later
record `quarantined` or `superseded` withdraws it. Only the newest usable version of a generator
enters a curriculum, so adding versions never adds weight.
"""

from __future__ import annotations

from pathlib import Path

from . import canon, policy as POL
from .records import Store


def versions(store: Store, base: Path, pol: dict, role: str | None = None) -> list[dict]:
    latest: dict[tuple, dict] = {}
    for r in store.read("certification"):
        latest[(r["family_id"], r["generator_id"], r["version"])] = r
    out = []
    for key, r in sorted(latest.items()):
        if role and r["role"] != role:
            continue
        state, why = r["status"], r["reason"]
        if state == "certified":
            fam = POL.family(pol, r["family_id"])
            if fam is None or fam["role"] != r["role"]:
                state, why = "incompatible", "family no longer approved for this role"
            elif (fam["revision"], fam["seed_bits"], fam["entropy_bits"]) != \
                    (r["family_revision"], r["seed_bits"], r["required_bits"]):
                state, why = "incompatible", "family revision, seed width or entropy changed"
            else:
                for path, sha in r["files"].items():
                    p = Path(base) / path
                    if p.is_symlink() or not p.is_file() or \
                            canon.sha256_bytes(p.read_bytes()) != sha:
                        state, why = "not_merged", f"{path} on main is not the certified file"
                        break
        out.append({"role": r["role"], "family_id": r["family_id"],
                    "generator_id": r["generator_id"], "version": r["version"],
                    "levels": r["levels"], "seed_bits": r["seed_bits"],
                    "entropy_bits": r["entropy_bits"], "required_bits": r["required_bits"],
                    "state": state, "reason": why, "certification_id": r["record_id"],
                    "path": r["path"], "bootstrap": r["bootstrap"]})
    return out


def usable(store: Store, base: Path, pol: dict, role: str) -> list[dict]:
    """The newest certified, merged, compatible version of each generator of `role`."""
    best: dict[tuple, dict] = {}
    for v in versions(store, base, pol, role):
        if v["state"] != "certified":
            continue
        k = (v["family_id"], v["generator_id"])
        if k not in best or v["version"] > best[k]["version"]:
            best[k] = v
    return [best[k] for k in sorted(best)]
