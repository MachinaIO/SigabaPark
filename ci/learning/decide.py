"""Verdicts: notebook comparisons (spec 8.6, 9.1) and the learning pull request check.

Comparison verdicts (method `cp-union-v1`, `LB = CP_lower(w,n,a/2) - CP_upper(l,n,a/2)`):

* incomplete (fewer complete pairs than planned, or an unresolved infrastructure error):
  `infra_error`, never promotable;
* candidate over the cap: `fail`;
* screen (no formal claim): promising when the paired difference is strictly positive, or the
  note is strictly shorter and `delta_hat >= -delta_NI` -> `inconclusive` / `screen_promising`
  (confirmation follows); otherwise `fail` / `screen_not_promising`;
* confirm / anchor: `pass_performance` when `LB > 0`; `pass_compression` when the note is
  strictly shorter (tokens, else bytes) and `LB >= -delta_NI`; otherwise `fail` when the matching
  upper bound shows it is not better (`UB <= 0`, or for a shorter note `UB < -delta_NI`), else
  `inconclusive`. A longer or equal note is never promoted on a tie;
* a passing confirm verdict whose evidence is provisional within-family (`fresh_seed`) becomes
  `inconclusive` unless the policy authorizes provisional activation.

The pull request check (`decide`) never merges: learning pull requests are never auto-merged; a
passing generator or notebook gets `learning:needs-maintainer` for the normal review.
"""

from __future__ import annotations

import json
from fractions import Fraction
from pathlib import Path

from . import activation as A, contract as C, policy as POL, records as RS, sampling, schema, \
    stats
from .records import Store

LABELS = ("learning:not-accepted", "learning:rejected", "learning:needs-maintainer",
          "learning:awaiting-evaluator", "learning:inconclusive")


def shorter(nb: dict) -> bool:
    ct, it = nb.get("candidate_tokens"), nb.get("incumbent_tokens")
    if ct is not None and it is not None:
        return ct < it
    return nb["candidate_bytes"] < nb["incumbent_bytes"]


def comparison_verdict(stage: str, counts: dict, planned: int, complete: bool, nb: dict,
                       pol: dict, scope: str, provisional: bool) -> tuple[str, str, dict]:
    """(verdict, reason, bounds)."""
    pr = pol["promotion"]
    alpha, delta = POL.prob(pr["alpha"]), POL.prob(pr["delta_ni"])
    n = counts["n"]
    bounds = stats.cp_union(counts["w"], counts["l"], n, alpha)
    if not complete or n != planned:
        return "infra_error", (f"incomplete: {n} of {planned} planned complete pairs; not "
                               "promotable"), bounds
    if nb["candidate_tokens"] is not None and nb["candidate_tokens"] > nb["cap_tokens"]:
        return "fail", "the candidate is over the notebook cap", bounds
    short = shorter(nb)
    if stage == "screen":
        d = Fraction(counts["w"] - counts["l"], n)
        if d > 0 or (short and d >= -delta):
            return "inconclusive", "screen_promising: continue to an independent confirmation", \
                bounds
        return "fail", "screen_not_promising", bounds
    lb, ub = bounds["lower_bound"], bounds["upper_bound"]
    if lb > 0:
        v, why = "pass_performance", f"LB = {lb:.4f} > 0"
    elif short and lb >= -float(delta):
        v, why = "pass_compression", f"strictly shorter and LB = {lb:.4f} >= -{float(delta)}"
    elif (short and ub < -float(delta)) or (not short and ub <= 0):
        return "fail", f"not better: LB = {lb:.4f}, UB = {ub:.4f}", bounds
    else:
        return "inconclusive", (f"LB = {lb:.4f}, UB = {ub:.4f}" +
                                ("" if short else "; a note that is not shorter needs LB > 0")), \
            bounds
    if stage == "confirm" and provisional and not pr["provisional_within_family"]:
        return "inconclusive", (why + "; the evidence is within-family (fresh_seed) and the "
                                "policy does not authorize provisional activation"), bounds
    if stage == "anchor":
        why += " (anchor assessment: never activates)"
    return v, why, bounds


def confirm_scope(pol: dict, role: str, reserved_pool_ok: bool) -> tuple[str, bool] | str:
    """(scope, provisional) of the confirmation, or why there is none."""
    if reserved_pool_ok:
        return "family_disjoint", False
    groups = {f["group"] for f in pol["families"] if f["role"] == role}
    if pol["promotion"]["require_family_disjoint"] and len(groups) >= 3:
        return ("at least three independent families exist, so the policy must reserve one for "
                "family-disjoint confirmation")
    if pol["promotion"]["provisional_within_family"]:
        return "fresh_seed", True
    return ("no family-disjoint confirmation pool, and the policy does not authorize provisional "
            "within-family activation: the candidate stays inconclusive")


# -- the pull request check ------------------------------------------------------------------------


def _decision(conclusion: str, labels: list[str], comment: str, records=(), quiet=False,
              **extra) -> dict:
    return {"conclusion": conclusion, "automerge": False, "labels": labels,
            "comment": comment[:60000], "records": list(records), "quiet": quiet, **extra}


def label_changes(current: list[str], wanted: list[str]) -> list[tuple[str, str]]:
    ops = [("add", l) for l in wanted if l not in current]
    ops += [("remove", l) for l in current if l in LABELS and l not in wanted]
    return ops


def decide(route: dict, *, certify: dict | None = None, exit_code: int | None = None,
           env: str | None = None, store: Store | None = None, base: Path | None = None,
           base_sha: str | None = None, created_at: str | None = None) -> dict:
    if schema.check(route, "route"):
        return _decision("failure", ["learning:rejected"],
                         "### Learning check\n\nThe precheck's output is not usable.")
    r = route["route"]
    if r == "skipped":
        return _decision("neutral", [], "Draft: the learning check runs when it is ready.",
                         quiet=True)
    if not route["accepted"]:
        return _decision("failure", ["learning:not-accepted"], "### Not accepted\n\n" +
                         "\n".join(f"- {p}" for p in route["problems"]))
    if r == "rejected":
        return _decision("failure", ["learning:rejected"], "### Learning precheck failed\n\n" +
                         "\n".join(f"- {p}" for p in route["problems"][:100]))
    if r == "math":
        return _decision("success", [], "Mathematical nodes only: the gate decides.", quiet=True)
    if r == "generator":
        return decide_generator(route, certify, exit_code, env, base, base_sha, created_at)
    return decide_notebook(route, store, base)


def decide_generator(route: dict, result: dict | None, exit_code: int | None, env: str | None,
                     base: Path | None, base_sha: str | None, created_at: str | None) -> dict:
    g = route["generator"]
    gid = f"{g['role']}/{g['family_id']}/{g['generator_id']}/v{g['version']:04d}"
    bad = []
    if result is None:
        bad.append("the certifier produced no result")
    elif probs := schema.check(result, "certify-result"):
        bad.append("the certifier's result does not have the expected shape: " +
                   "; ".join(probs[:10]))
    else:
        if exit_code not in (0, 1):
            bad.append(f"the certifier exited with {exit_code}")
        if result["revision"] != route["revision"]:
            bad.append(f"the result is about {result['revision']}, not {route['revision']}")
        if env is not None and result["env"] != env:
            bad.append(f"the result is about environment {result['env']}, not {env}")
        if result["generator"] != {k: g[k] for k in ("role", "family_id", "generator_id",
                                                      "version")}:
            bad.append("the result is about another generator")
        if result["files"] != g["files"]:
            bad.append("the result's file hashes are not the precheck's")
        ok = (not result["problems"] and result["build"]["ok"] and
              result["lean_result"]["verdict"] == "verified" and result["smoke"] and
              all(s["status"] == "ok" for s in result["smoke"]))
        if ok != (result["status"] == "certified") or (exit_code == 0) != ok:
            bad.append("the result's status contradicts its contents or the exit status")
        levels = {s["level"] for s in result["smoke"] if s["status"] == "ok"}
        if ok and levels != set(range(g["levels"])):
            bad.append("the smoke test does not cover every level")
        ctx = _smoke_ctx(g, route["revision"])
        if [(i["seed_commitment"], i["level"]) for i in result["reveal"]] != \
                [(s["seed_commitment"], s["level"]) for s in result["smoke"]] or \
                not all(sampling.verify_reveal(ctx, i) for i in result["reveal"]):
            bad.append("the smoke seeds do not match their commitments")
    if bad:
        return _decision("failure", [], f"### Generator `{gid}`: the certifier's result is not "
                         "usable\n\n" + "\n".join(f"- {p}" for p in bad))
    certified = result["status"] == "certified"
    pol = POL.load_base(base) if base is not None else None
    records = []
    if pol is not None and created_at is not None:
        reason = "universal certificate checked; smoke samples ok" if certified else \
            "; ".join(result["lean_result"]["problems"][:5] + result["problems"][:5])[:4000] \
            or "rejected"
        cert = {"schema": "sigaba.learning.certification.v1", "role": g["role"],
                "family_id": g["family_id"], "family_revision": g["family_revision"],
                "generator_id": g["generator_id"], "version": g["version"], "path": g["dir"],
                "pr": route["pr"], "head": route["revision"], "author": route["author"],
                "files": g["files"], "seed_bits": g["seed_bits"], "levels": g["levels"],
                "entropy_bits": g["entropy_bits"] if certified else 0,
                "required_bits": g["entropy_bits"], "equivalence": None,
                "certificate_decl": g["certificate_decl"], "generate_decl": g["generate_decl"],
                "lean_result": result["lean_result"], "smoke": result["smoke"],
                "status": "certified" if certified else "rejected", "reason": reason,
                "source_refs": g["source_refs"], "bootstrap": g["bootstrap"]}
        cert = RS.stamp(cert, created_at, C.common(pol, base_sha))
        rev = RS.stamp({"schema": "sigaba.learning.reveal.v1", "contract_id": cert["record_id"],
                        "items": result["reveal"]}, created_at, C.common(pol, base_sha))
        records = [cert, rev]
    lines = [f"### Generator `{gid}`: " + ("certified" if certified else "rejected"), "",
             f"- Lean check: `{result['lean_result']['verdict']}` (L = {g['levels']}, "
             f"k = {g['seed_bits']}, required h = {g['entropy_bits']} bits from the family "
             "policy)",
             f"- Smoke samples: {sum(1 for s in result['smoke'] if s['status'] == 'ok')} ok of "
             f"{len(result['smoke'])} (runtime sanity only; never a source of entropy)"]
    lines += [f"- {p}" for p in (result["lean_result"]["problems"] + result["problems"])[:50]]
    if certified:
        lines.append("\nCertified. Learning pull requests are never merged automatically: a "
                     "maintainer reviews and merges it.")
    return _decision("success" if certified else "failure",
                     ["learning:needs-maintainer"] if certified else ["learning:rejected"],
                     "\n".join(lines), records)


def _smoke_ctx(g: dict, revision: str | None) -> str:
    from .certify import smoke_context
    return smoke_context(g, revision)


def decide_notebook(route: dict, store: Store | None, base: Path | None) -> dict:
    nb = route["notebook"]
    head = None if route["event"] == "merge_group" else route["revision"]
    try:
        pol = POL.load_base(base)
        state = A.active(store, nb["role"])
    except (POL.PolicyError, A.ActivationError, RS.RecordError, TypeError) as e:
        return _decision("failure", ["learning:needs-maintainer"],
                         f"### Notebook `{nb['path']}`\n\nThe learning state is not usable: {e}")
    if state["active"] != nb["incumbent_sha256"]:
        return _decision("failure", ["learning:needs-maintainer"],
                         f"### Notebook `{nb['path']}`\n\nThe notebook on main "
                         f"({nb['incumbent_sha256']}) is not the replayed active notebook "
                         f"({state['active']}); a maintainer must reconcile them.")
    comp, why = A.find_valid(store, pol, nb["role"], nb["sha256"], nb["incumbent_sha256"], head)
    size = (f"{nb['bytes']} bytes, {nb['tokens']} tokens ({nb['tokenizer']['kind']} proxy); "
            f"active notebook {nb['incumbent_bytes']} bytes, {nb['incumbent_tokens']} tokens")
    if comp is not None:
        return _decision("success", ["learning:needs-maintainer"], "\n".join([
            f"### Notebook `{nb['path']}`: `{comp['verdict']}`", "",
            f"- Scope: `{comp['scope']}`" + (" (provisional)" if comp["provisional"] else ""),
            f"- Pairs: {comp['n']}, wins {comp['w']}, losses {comp['l']}, "
            f"delta_hat {comp['delta_hat']:.4f}, LB {comp['lower_bound']:.4f} "
            f"({comp['method']}, alpha {comp['alpha']})",
            f"- Size: {size}", f"- Comparison: `{comp['record_id']}`", "",
            "A passing verdict is not permission to merge: a maintainer merges it, and the "
            "activation re-checks the incumbent (compare-and-swap)."]),
            comparison_id=comp["record_id"])
    pending = [c for c in store.read("comparison") if c["role"] == nb["role"] and
               c["candidate_sha256"] == nb["sha256"]]
    label = "learning:awaiting-evaluator"
    if pending and pending[-1]["verdict"] in ("fail", "inconclusive", "infra_error") and \
            pending[-1]["incumbent_sha256"] == nb["incumbent_sha256"]:
        label = "learning:inconclusive" if pending[-1]["verdict"] != "fail" else \
            "learning:rejected"
    return _decision("failure", [label], "\n".join(
        [f"### Notebook `{nb['path']}`: no valid passing comparison", "", f"- Size: {size}"] +
        [f"- {w}" for w in why[:10]] +
        ["", "The trusted evaluator compares it with the active notebook (screen, then an "
         "independent confirmation). Until a valid confirm verdict exists for this exact head "
         "and incumbent, this check fails."]))


def load_json(path: Path | None) -> dict | None:
    if path is None:
        return None
    try:
        return json.loads(Path(path).read_text())
    except (OSError, json.JSONDecodeError):
        return None


def read_exit(path: Path | None) -> int | None:
    if path is None:
        return None
    try:
        return int(Path(path).read_text().strip())
    except (OSError, ValueError):
        return None

