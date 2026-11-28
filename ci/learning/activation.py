"""Notebook activation: append-only events, compare-and-swap, deterministic replay (spec 10.2-10.3).

The active notebook of a role is derived, never asserted: replaying `activations.jsonl` in order
gives, per role, the hash of the active notebook (initially the empty notebook). Each event must
carry `sequence` = previous + 1 and name the currently active hash as `predecessor_sha256`
(compare-and-swap); a history that breaks either rule is an error (fail closed). The notebook file
on `main` must equal the replayed active hash; `status` and `doctor` report a mismatch.

`activate` runs on a push to `main` after a notebook merge. It appends an event only when

* a valid confirm comparison exists for exactly this candidate (hash and head) against exactly
  the active notebook, under the current policy and epoch, with a promotable scope (`improvement`
  or `compression`); a second candidate evaluated against the same old incumbent then fails the
  swap and must be re-evaluated; or
* an admin/maintainer restores the exact bytes of an earlier active notebook (`rollback`, never
  shown as an empirical improvement); or
* an admin/maintainer explicitly seeds the first notebook of a role (`bootstrap`).

`verdict_status` is the staleness rule: a passing verdict counts only for the exact candidate and
head, the current active incumbent, and the current policy (id and digest) and epoch.
"""

from __future__ import annotations

from pathlib import Path

from . import canon, contract as C, notebooks as NB, policy as POL, records as RS, stats
from .records import Store

MAINTAINERS = ("admin", "maintain")
PASSING = ("pass_performance", "pass_compression")


class ActivationError(Exception):
    pass


def replay(events: list[dict]) -> dict[str, dict]:
    state = {r: {"active": NB.EMPTY_SHA256, "sequence": 0, "history": [NB.EMPTY_SHA256],
                 "events": []} for r in NB.ROLES}
    for e in events:
        s = state[e["role"]]
        if e["sequence"] != s["sequence"] + 1:
            raise ActivationError(f"activation {e['record_id']}: sequence {e['sequence']} after "
                                  f"{s['sequence']} for {e['role']}")
        pred = e["predecessor_sha256"] or NB.EMPTY_SHA256
        if pred != s["active"]:
            raise ActivationError(f"activation {e['record_id']}: predecessor {pred} is not the "
                                  f"active notebook {s['active']} (compare-and-swap)")
        s["active"] = e["successor_sha256"]
        s["sequence"] = e["sequence"]
        s["history"].append(e["successor_sha256"])
        s["events"].append(e)
    return state


def active(store: Store, role: str) -> dict:
    return replay(store.read("activation"))[role]


def recompute(store: Store, comp: dict) -> list[str]:
    """Why a comparison does not follow from its trial records (missing, duplicate or foreign
    trials, wrong arms, incomplete set, aggregates that do not match)."""
    trials = {t["record_id"]: t for t in store.read("trial")}
    con = next((c for c in store.read("contract") if c["contract_id"] == comp["contract_id"]),
               None)
    if con is None:
        return ["its contract is not recorded"]
    probs, pairs, used, pair_ids = [], [], set(), set()
    for a, b in comp["pair_refs"]:
        ta, tb = trials.get(a), trials.get(b)
        if ta is None or tb is None:
            probs.append("a referenced trial is missing")
            continue
        if a in used or b in used:
            probs.append("a trial is referenced twice")
        used |= {a, b}
        if ta["contract_id"] != comp["contract_id"] or tb["contract_id"] != comp["contract_id"]:
            probs.append("a trial belongs to another contract")
        if ta["run_id"] != tb["run_id"] or ta["pair_id"] != tb["pair_id"] or \
                ta["pair_id"] in pair_ids:
            probs.append("a pair's trials do not match (run, pair id) or a pair repeats")
        pair_ids.add(ta["pair_id"])
        want = ("anchor_baseline", "incumbent") if comp["stage"] == "anchor" else \
            ("incumbent", "candidate")
        if (ta["arm"], tb["arm"]) != want:
            probs.append("a pair's arms are wrong")
        if (ta["seed_commitment"], ta["descriptor_sha256"]) != \
                (tb["seed_commitment"], tb["descriptor_sha256"]):
            probs.append("a pair's arms did not get the same task")
        if "infra_error" in (ta["outcome"], tb["outcome"]):
            probs.append("a pair has an unresolved infrastructure error")
        pairs.append((int(ta["outcome"] == "solved"), int(tb["outcome"] == "solved")))
    counts = stats.paired_counts(pairs)
    for k, v in counts.items():
        if comp[k] != v:
            probs.append(f"`{k}` is {comp[k]}, the trials give {v}")
    if comp["verdict"] in PASSING and counts["n"] != con["trials_planned"]:
        probs.append("a passing verdict needs the planned number of complete pairs")
    return probs


def promotable_scope(comp: dict, pol: dict) -> bool:
    if comp["scope"] in ("family_disjoint", "future_family") and not comp["provisional"]:
        return True
    return comp["provisional"] and pol["promotion"]["provisional_within_family"]


def verdict_status(store: Store, comp: dict, pol: dict, candidate_sha: str, incumbent_sha: str,
                   head: str | None) -> tuple[bool, str]:
    if comp["stage"] != "confirm":
        return False, "not a confirm comparison"
    if comp["verdict"] not in PASSING:
        return False, f"verdict {comp['verdict']}"
    if comp["candidate_sha256"] != candidate_sha:
        return False, "stale: the candidate notebook changed"
    if head is not None and comp["head"] != head:
        return False, "stale: the pull request's head changed"
    if comp["incumbent_sha256"] != incumbent_sha:
        return False, "stale: the active notebook changed (re-evaluate against the new incumbent)"
    con = next((c for c in store.read("contract") if c["contract_id"] == comp["contract_id"]),
               None)
    if con is None:
        return False, "its contract is not recorded"
    if comp["policy_id"] != pol["policy_id"] or con["policy_sha256"] != POL.sha256(pol):
        return False, "stale: the learning policy changed"
    if comp["epoch_id"] != pol["epoch"]["id"] or con["epoch_id"] != pol["epoch"]["id"]:
        return False, "stale: the evaluation epoch changed"
    if not promotable_scope(comp, pol):
        return False, "provisional within-family evidence is not authorized by the policy"
    if probs := recompute(store, comp):
        return False, "the comparison does not follow from its trials: " + "; ".join(probs[:5])
    return True, "valid"


def find_valid(store: Store, pol: dict, role: str, candidate_sha: str, incumbent_sha: str,
               head: str | None) -> tuple[dict | None, list[str]]:
    why = []
    for comp in reversed(store.read("comparison")):
        if comp["role"] != role or comp["candidate_sha256"] != candidate_sha:
            continue
        ok, reason = verdict_status(store, comp, pol, candidate_sha, incumbent_sha, head)
        if ok:
            return comp, []
        why.append(f"{comp['record_id'][:19]} ({comp['stage']}): {reason}")
    return None, why or ["no comparison of this notebook"]


def activate(store: Store, base: Path, pol: dict, role: str, merge_commit: str, pr: int | None,
             head: str | None, actor: str, permission: str, created_at: str,
             bootstrap: bool = False) -> dict:
    """The activation event for the notebook now on `main` (`{"status": ...}` plus `record`
    when one is to be appended). Raises `ActivationError` when the merge has no valid basis."""
    data = NB.read_active_file(base, role)
    succ = canon.sha256_bytes(data)
    st = active(store, role)
    pred = st["active"]
    if succ == pred:
        return {"status": "unchanged", "active": pred, "record": None}
    ev = {"schema": "sigaba.learning.activation.v1", "role": role, "predecessor_sha256": pred,
          "successor_sha256": succ, "pr": pr, "head": head, "merge_commit": merge_commit,
          "policy_id": pol["policy_id"], "epoch_id": pol["epoch"]["id"], "actor": actor,
          "sequence": st["sequence"] + 1, "anchor_refs": _anchor_refs(store, pol, role)}
    comp, why = find_valid(store, pol, role, succ, pred, head)
    if comp is not None:
        screens = [c["record_id"] for c in store.read("comparison")
                   if c["stage"] == "screen" and c["candidate_sha256"] == succ and
                   c["head"] == comp["head"] and c["incumbent_sha256"] == pred]
        ev.update(comparison_ids=screens[-1:] + [comp["record_id"]], scope=comp["scope"],
                  provisional=comp["provisional"],
                  reason="improvement" if comp["verdict"] == "pass_performance"
                  else "compression")
    elif permission in MAINTAINERS and succ in st["history"]:
        prior = next((e for e in reversed(st["events"]) if e["successor_sha256"] == succ), None)
        ev.update(comparison_ids=[], reason="rollback",
                  scope=prior["scope"] if prior else "fresh_seed",
                  provisional=prior["provisional"] if prior else True)
    elif bootstrap and permission in MAINTAINERS and st["sequence"] == 0:
        ev.update(comparison_ids=[], reason="bootstrap", scope="fresh_seed", provisional=True)
    else:
        raise ActivationError(
            f"the {role} notebook on main ({succ}) has no valid basis for activation: "
            + "; ".join(why[:5]) + ("" if permission in MAINTAINERS else
                                    f"; @{actor} (permission {permission}) cannot roll back"))
    return {"status": "activated", "active": succ,
            "record": RS.stamp(ev, created_at, C.common(pol))}


def _anchor_refs(store: Store, pol: dict, role: str) -> list[str]:
    comps = [c for c in store.read("comparison") if c["role"] == role and
             c["stage"] == "anchor" and c["epoch_id"] == pol["epoch"]["id"]]
    return [c["record_id"] for c in comps[-1:]]


def consistency(store: Store, base: Path) -> dict[str, dict]:
    """Per role: the replayed active hash, the file on `main`, and whether they agree."""
    st = replay(store.read("activation"))
    out = {}
    for r in NB.ROLES:
        main = canon.sha256_bytes(NB.read_active_file(base, r))
        out[r] = {"active": st[r]["active"], "main": main, "sequence": st[r]["sequence"],
                  "consistent": main == st[r]["active"]}
    return out
