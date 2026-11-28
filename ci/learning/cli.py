"""The learning extension's command line (run from the repository root):

    python3 -m ci.learning.cli <command> [flags]

Every command prints one JSON object on standard output (errors as `{"error": ...}` with exit
status 2) and never prints a token or secret. Commands that produce records only append them to
the store (`--records`, a checkout of the branch `learning-records`) with `--publish`; otherwise
the records are part of the JSON output. Run `<command> --help` for the flags.

Precheck and PR check (trusted, no pull request code):
    fetch, route, decide (alias decide-generator), labels, publish
Sandbox (inside the environment image, no network):
    certify
Trusted evaluator (maintainer-authorized runner):
    evaluate, calibrate, anchor
On push to main:
    activate
Read only:
    status, inspect, generator-list, sources, doctor, report
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from pathlib import Path

from . import activation as A, canon, curriculum as CU, decide as DE, evaluate as EV, \
    lean_iface as LI, notebooks as NB, policy as POL, records as RS, registry, route as RT, \
    schema, sources


class CliError(Exception):
    pass


def emit(obj, out: str | None = None) -> None:
    text = json.dumps(obj, indent=1, sort_keys=True) + "\n"
    if out and out != "-":
        Path(out).write_text(text)
    sys.stdout.write(text if not out or out == "-" else
                     json.dumps(_summary(obj), sort_keys=True) + "\n")


def _summary(obj) -> dict:
    if not isinstance(obj, dict):
        return {"ok": True}
    keep = ("route", "ok", "status", "verdict", "reason", "conclusion", "labels")
    s = {k: obj[k] for k in keep if k in obj}
    if "records" in obj:
        s["records"] = len(obj["records"])
    return s


def bool_arg(s: str) -> bool:
    if s.lower() in ("true", "1", "yes"):
        return True
    if s.lower() in ("false", "0", "no", ""):
        return False
    raise argparse.ArgumentTypeError("true or false")


def store_of(d: str | None) -> RS.Store:
    return RS.Store(Path(d) if d else None)


def publish(store: RS.Store, recs: list[dict], do: bool) -> list[str]:
    if not do:
        return []
    return [r["record_id"] for r in store.append(recs)]


# -- precheck --------------------------------------------------------------------------------------


def cmd_fetch(a) -> int:
    from . import fetch
    rows = fetch.main(a.repo, a.base, a.head, Path(a.out))
    emit({"ok": True, "revision": a.head, "files": len(rows),
          "downloaded": sum(1 for _ in (Path(a.out) / "files").rglob("*") if _.is_file())
          if (Path(a.out) / "files").is_dir() else 0})
    return 0


def cmd_fetch_local(a) -> int:
    from . import fetch
    rows = fetch.fetch_local(Path(a.repo_dir), a.base, a.head, Path(a.out))
    emit({"ok": True, "revision": a.head, "files": len(rows)})
    return 0


def cmd_split_versions(a) -> int:
    from . import fetch
    emit({"ok": True, "versions": fetch.split_versions(Path(a.fetched), Path(a.dir))}, a.out)
    return 0


def cmd_route(a) -> int:
    r = RT.route(Path(a.base), Path(a.fetched), a.author, a.permission, a.draft, a.event,
                 a.pr, Path(a.records) if a.records else None)
    emit(r, a.out)
    return 0


def cmd_decide(a) -> int:
    route = DE.load_json(Path(a.route))
    if route is None:
        route = {"schema": "invalid"}
    d = DE.decide(route, certify=DE.load_json(Path(a.certify)) if a.certify else None,
                  exit_code=DE.read_exit(Path(a.exit_code)) if a.exit_code else None,
                  env=a.env, store=store_of(a.records), base=Path(a.base) if a.base else None,
                  base_sha=a.base_sha, created_at=canon.now())
    emit(d, a.out)
    return 0


def cmd_labels(a) -> int:
    d = json.loads(Path(a.decision).read_text())
    current = json.loads(a.current)
    for op, label in DE.label_changes(current, d["labels"]):
        print(op, label)
    return 0


def cmd_publish(a) -> int:
    store = store_of(a.records)
    recs = []
    for f in a.input:
        text = Path(f).read_text()
        if f.endswith(".jsonl"):
            recs += [json.loads(l) for l in text.splitlines() if l.strip()]
        else:
            obj = json.loads(text)
            recs += obj.get("records", []) if isinstance(obj, dict) else obj
    written = store.append(recs)
    emit({"ok": True, "written": [r["record_id"] for r in written],
          "skipped": len(recs) - len(written)})
    return 0


# -- sandbox ---------------------------------------------------------------------------------------


def cmd_certify(a) -> int:
    from .certify import certify
    route = json.loads(Path(a.route).read_text())
    res = certify(route, Path(a.files), Path(a.core), Path(a.workdir), a.smoke_seeds,
                  a.timeout, a.env)
    emit(res, a.out)
    return 0 if res["status"] == "certified" else 1


# -- evaluator -------------------------------------------------------------------------------------


class _MockSampler(EV.Sampler):
    """Dry runs only: a deterministic stand-in descriptor (no Lean)."""

    def sample(self, gen, level, seed):
        h = hashlib.sha256(f"{gen['generator_id']}:{level}:{seed}".encode()).digest()
        return "".join(f"{b:08b}" for b in h[:4])


class _RejectAll(EV.Verifier):
    def verify(self, req, solution):
        return {"verdict": "rejected", "theorem_sha256": None, "certified_value": None}


def _evaluator(a, pol: dict, role: str):
    profile = POL.profile(pol, role)
    if a.dry_run:
        pol = json.loads(json.dumps(pol))
        pol["evaluator"]["max_trials_per_run"] = 10 ** 6
        if profile is None:
            profile = {"profile_id": "dry-run", "role": role, "provider": "mock",
                       "model": "mock-1", "settings": {},
                       "budget": {"max_model_calls": 1, "max_input_tokens": 1,
                                  "max_output_tokens": 1, "wall_seconds": 1, "lean_seconds": 1}}
            pol["profiles"] = [p for p in pol["profiles"] if p["role"] != role] + [profile]
        return pol, EV.MockProvider(), "dry run", _MockSampler(), _RejectAll()
    provider, note = EV.provider_for(pol, profile, False)
    if provider is None:
        return pol, None, note, None, None
    if not a.core or not a.workdir:
        raise CliError("--core and --workdir are needed to sample and verify with Lean")
    work = Path(a.workdir)
    counter = iter(range(10 ** 9))
    sampler = EV.LeanSampler(lambda ns: LI.Workspace(work / "generators" / ns, Path(a.core)),
                             Path(a.base), pol)
    verifier = EV.LeanTaskVerifier(lambda: LI.Workspace(work / f"answer-{next(counter):06d}",
                                                        Path(a.core), libs=("Answers",)))
    return pol, provider, note, sampler, verifier


def _as_of(a) -> float | None:
    return canon.parse_time(a.as_of) if getattr(a, "as_of", None) else None


def cmd_evaluate(a) -> int:
    base, store = Path(a.base), store_of(a.records)
    route = json.loads(Path(a.route).read_text())
    if schema.check(route, "route") or route["route"] != "notebook" or not route["ok"]:
        raise CliError("the route is not an admitted notebook pull request")
    nb = route["notebook"]
    cand = Path(a.fetched) / "files" / nb["path"]
    pol = POL.load_base(base)
    pol, provider, note, sampler, verifier = _evaluator(a, pol, nb["role"])
    res = EV.evaluate_notebook(store=store, base=base, pol=pol, route=route,
                               candidate=cand.read_bytes(), provider=provider,
                               provider_note=note, sampler=sampler, verifier=verifier,
                               as_of=_as_of(a))
    res["dry_run"] = a.dry_run
    res["published"] = publish(store, res["records"], a.publish and not a.dry_run)
    emit(res, a.out)
    return 0


def cmd_calibrate(a) -> int:
    base, store = Path(a.base), store_of(a.records)
    pol = POL.load_base(base)
    pol, provider, note, sampler, verifier = _evaluator(a, pol, a.role)
    res = EV.calibrate(store=store, base=base, pol=pol, role=a.role, provider=provider,
                       provider_note=note, sampler=sampler, verifier=verifier, budget=a.budget,
                       as_of=_as_of(a))
    res["dry_run"] = a.dry_run
    res["published"] = publish(store, res["records"], a.publish and not a.dry_run)
    emit(res, a.out)
    return 0


def cmd_anchor(a) -> int:
    base, store = Path(a.base), store_of(a.records)
    pol = POL.load_base(base)
    pol, provider, note, sampler, verifier = _evaluator(a, pol, a.role)
    res = EV.anchor(store=store, base=base, pol=pol, role=a.role, anchor_epoch=a.epoch,
                    provider=provider, provider_note=note, sampler=sampler, verifier=verifier,
                    as_of=_as_of(a), pairs=a.pairs)
    res["dry_run"] = a.dry_run
    res["published"] = publish(store, res["records"], a.publish and not a.dry_run)
    emit(res, a.out)
    return 0


# -- activation ------------------------------------------------------------------------------------


def cmd_activate(a) -> int:
    base, store = Path(a.base), store_of(a.records)
    pol = POL.load_base(base)
    roles = NB.ROLES if a.role == "auto" else (a.role,)
    out, status, recs = {"results": {}}, 0, []
    for role in roles:
        try:
            r = A.activate(store, base, pol, role, a.merge_commit, a.pr, a.head, a.actor,
                           a.permission, canon.now(), a.bootstrap)
        except A.ActivationError as e:
            out["results"][role] = {"status": "error", "reason": str(e)[:4000]}
            status = 1
            continue
        out["results"][role] = {"status": r["status"], "active": r["active"]}
        if r["record"] is not None:
            recs.append(r["record"])
    out["records"] = recs
    out["published"] = publish(store, recs, a.publish)
    out["status"] = "error" if status else "ok"
    emit(out, a.out)
    return status


# -- read only -------------------------------------------------------------------------------------


def cmd_status(a) -> int:
    base, store = Path(a.base), store_of(a.records)
    pol = POL.load_base(base)
    out = {"policy_id": pol["policy_id"], "epoch_id": pol["epoch"]["id"],
           "evaluator": pol["evaluator"], "adversary_model": "classical", "roles": {}}
    try:
        cons = A.consistency(store, base)
    except A.ActivationError as e:
        cons = {r: {"error": str(e)} for r in NB.ROLES}
    for role in ([a.role] if a.role else NB.ROLES):
        gens = registry.versions(store, base, pol, role)
        comps = [c for c in store.read("comparison") if c["role"] == role]
        prof = POL.profile(pol, role)
        sel = []
        if prof is not None:
            ref = cons[role].get("active", NB.EMPTY_SHA256)
            arms = CU.aggregate(store.read("calibration"), role, prof["profile_id"], ref,
                                pol["curriculum"]["stale_after_days"], _as_of(a))
            sel = CU.select(registry.usable(store, base, pol, role), arms, pol)
        out["roles"][role] = {
            "notebook": cons[role],
            "generators": {s: sum(1 for g in gens if g["state"] == s)
                           for s in sorted({g["state"] for g in gens})},
            "curriculum": sel,
            "comparisons": [{k: c[k] for k in ("record_id", "stage", "verdict", "pr", "head",
                                                "scope", "provisional", "n", "created_at")}
                            for c in comps[-10:]]}
    emit(out, a.out)
    return 0


def cmd_inspect(a) -> int:
    store = store_of(a.records)
    out: dict = {}
    if a.record:
        out["record"] = store.get(a.record)
    if a.contract:
        out["contract"] = next((c for c in store.read("contract")
                                if c["contract_id"] == a.contract), None)
        out["comparisons"] = [c for c in store.read("comparison")
                              if c["contract_id"] == a.contract]
        out["trials"] = [t["record_id"] for t in store.read("trial")
                         if t["contract_id"] == a.contract]
        out["reveals"] = [r["record_id"] for r in store.read("reveal")
                          if r["contract_id"] == a.contract]
    if a.run:
        ts = [t for t in store.read("trial") if t["run_id"] == a.run]
        out["run"] = {"trials": ts, "contracts": sorted({t["contract_id"] for t in ts})}
    emit(out, a.out)
    return 0


def cmd_generator_list(a) -> int:
    base, store = Path(a.base), store_of(a.records)
    pol = POL.load_base(base)
    emit({"generators": registry.versions(store, base, pol, a.role)}, a.out)
    return 0


def cmd_sources(a) -> int:
    pol = POL.load_base(Path(a.dag))
    env = a.env or pol["epoch"]["environment_id"]
    commit = a.commit or pol["epoch"]["dag_snapshot"]
    nodes = sources.corpus(Path(a.dag), Path(a.dag_records) if a.dag_records else None, env,
                           commit)
    out = sources.sample(nodes, a.role, a.seed, a.count)
    out["env"] = env
    if a.validate:
        man = json.loads(Path(a.validate).read_text())
        out["validation"] = sources.ref_problems(man.get("source_refs", []), nodes)
    emit(out, a.out)
    return 0


def cmd_doctor(a) -> int:
    base = Path(a.base)
    checks = {}
    try:
        pol = POL.load_base(base)
        checks["policy"] = {"ok": True, "policy_id": pol["policy_id"],
                            "sha256": POL.sha256(pol)}
        envs = json.loads((base / "env" / "environments.json").read_text())["environments"]
        checks["environment"] = {"ok": any(e["id"] == pol["epoch"]["environment_id"]
                                           for e in envs),
                                 "id": pol["epoch"]["environment_id"]}
        sd = POL.strength_digest(base)
        checks["strengths"] = {"ok": sd == pol["epoch"]["strength_digest"], "current": sd,
                               "epoch": pol["epoch"]["strength_digest"]}
        ev = pol["evaluator"]
        prov = {r: EV.provider_for(pol, POL.profile(pol, r), False)[1] or "authorized"
                for r in NB.ROLES}
        checks["evaluator"] = {"ok": True, "enabled": ev["enabled"], "provider": ev["provider"],
                               "roles": prov}
        for r in NB.ROLES:
            data = NB.read_active_file(base, r)
            checks[f"notebook:{r}"] = {"ok": not NB.problems(data, pol),
                                       "problems": NB.problems(data, pol),
                                       **NB.measure(data, pol)}
    except (POL.PolicyError, OSError, ValueError, KeyError) as e:
        checks["policy"] = {"ok": False, "error": str(e)[:4000]}
    for name in schema.KINDS.values():
        try:
            schema.validate({}, schema.load(name))
        except (ValueError, OSError) as e:
            checks[f"schema:{name}"] = {"ok": False, "error": str(e)}
    if a.records:
        store = store_of(a.records)
        probs = store.verify()
        try:
            cons = A.consistency(store, base)
        except (A.ActivationError, RS.RecordError) as e:
            cons, probs = {}, probs + [str(e)]
        checks["records"] = {"ok": not probs and all(c["consistent"] for c in cons.values()),
                             "problems": probs, "notebooks": cons}
    checks["python"] = {"ok": sys.version_info >= (3, 10), "version": sys.version.split()[0]}
    emit({"ok": all(c.get("ok") for c in checks.values()), "checks": checks,
          "repo": a.repo}, a.out)
    return 0


def cmd_report(a, rest: list[str]) -> int:
    try:
        from .report import main as report_main
    except ImportError as e:
        raise CliError(f"the report generator is not installed: {e}") from None
    return report_main(rest) or 0


# -- arguments -------------------------------------------------------------------------------------


def parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(prog="python3 -m ci.learning.cli")
    sub = p.add_subparsers(dest="cmd", required=True)

    def add(name, fn, help, **kw):
        s = sub.add_parser(name, help=help, **kw)
        s.set_defaults(fn=fn)
        s.add_argument("--out", default="-", help="output file (default: standard output)")
        return s

    s = add("fetch", cmd_fetch, "fetch a pull request's changed files as data (GitHub API)")
    s.add_argument("--repo", required=True)
    s.add_argument("--base", required=True)
    s.add_argument("--head", required=True)
    s.set_defaults(out=None)
    s._option_string_actions["--out"].required = True

    s = add("fetch-local", cmd_fetch_local, "the same as fetch, from a local checkout with both "
            "commits (post-merge)")
    s.add_argument("--repo-dir", default=".")
    s.add_argument("--base", required=True)
    s.add_argument("--head", required=True)
    s.set_defaults(out=None)
    s._option_string_actions["--out"].required = True

    s = add("split-versions", cmd_split_versions, "one listing per generator version added by "
            "a push (post-merge)")
    s.add_argument("--fetched", required=True)
    s.add_argument("--dir", required=True)

    s = add("route", cmd_route, "learning precheck: math, generator, notebook, rejected, skipped")
    s.add_argument("--base", required=True, help="base checkout (main)")
    s.add_argument("--fetched", required=True, help="output directory of `fetch`")
    s.add_argument("--author", required=True)
    s.add_argument("--permission", default="", help="the author's GitHub permission")
    s.add_argument("--draft", type=bool_arg, default=False)
    s.add_argument("--event", default="pull_request_target")
    s.add_argument("--pr", type=int)
    s.add_argument("--records", help="checkout of the DAG's `records` branch (source refs)")

    for name in ("decide", "decide-generator"):
        s = add(name, cmd_decide, "the learning check's decision (decision.json)")
        s.add_argument("--route", required=True)
        s.add_argument("--certify", help="certify's output (generator pull requests)")
        s.add_argument("--exit-code", help="file holding certify's exit status")
        s.add_argument("--env")
        s.add_argument("--records", help="checkout of `learning-records`")
        s.add_argument("--base", required=True)
        s.add_argument("--base-sha")

    s = add("labels", cmd_labels, "label operations for a decision")
    s.add_argument("--decision", required=True)
    s.add_argument("--current", required=True, help="JSON list of the current labels")

    s = add("publish", cmd_publish, "append the records of outputs to the record store")
    s.add_argument("--records", required=True)
    s.add_argument("input", nargs="+")

    s = add("certify", cmd_certify, "certify a generator version (inside the sandbox image)")
    s.add_argument("--route", required=True)
    s.add_argument("--files", required=True, help="fetched files root (repository paths)")
    s.add_argument("--core", default="/core")
    s.add_argument("--workdir", required=True)
    s.add_argument("--env")
    s.add_argument("--smoke-seeds", type=int, default=2)
    s.add_argument("--timeout", type=float, default=1800)

    def evaluator_flags(s):
        s.add_argument("--base", required=True)
        s.add_argument("--records", required=True)
        s.add_argument("--dry-run", action="store_true")
        s.add_argument("--publish", action="store_true")
        s.add_argument("--core")
        s.add_argument("--workdir")
        s.add_argument("--as-of")

    s = add("evaluate", cmd_evaluate, "screen and confirm a notebook pull request")
    s.add_argument("--route", required=True)
    s.add_argument("--fetched", required=True)
    evaluator_flags(s)

    s = add("calibrate", cmd_calibrate, "one bounded calibration batch for a role")
    s.add_argument("--role", required=True, choices=NB.ROLES)
    s.add_argument("--budget", type=int)
    evaluator_flags(s)

    s = add("anchor", cmd_anchor, "anchor assessment of the active notebook")
    s.add_argument("--role", required=True, choices=NB.ROLES)
    s.add_argument("--epoch", required=True)
    s.add_argument("--pairs", type=int)
    evaluator_flags(s)

    s = add("activate", cmd_activate, "record the activation of a merged notebook")
    s.add_argument("--role", default="auto", choices=NB.ROLES + ("auto",))
    s.add_argument("--base", required=True, help="checkout of main at the merge commit")
    s.add_argument("--records", required=True)
    s.add_argument("--merge-commit", required=True)
    s.add_argument("--pr", type=int)
    s.add_argument("--head")
    s.add_argument("--actor", required=True)
    s.add_argument("--permission", required=True)
    s.add_argument("--bootstrap", action="store_true")
    s.add_argument("--publish", action="store_true")

    s = add("status", cmd_status, "learning status per role")
    s.add_argument("--role", choices=NB.ROLES)
    s.add_argument("--base", required=True)
    s.add_argument("--records")
    s.add_argument("--as-of")

    s = add("inspect", cmd_inspect, "records of a run, contract or record id")
    s.add_argument("--records", required=True)
    s.add_argument("--run")
    s.add_argument("--contract")
    s.add_argument("--record")

    s = add("generator-list", cmd_generator_list, "the generator registry")
    s.add_argument("--role", choices=NB.ROLES)
    s.add_argument("--base", required=True)
    s.add_argument("--records")

    s = add("sources", cmd_sources, "sample verified DAG sources for generator development")
    s.add_argument("--role", required=True, choices=NB.ROLES)
    s.add_argument("--dag", required=True)
    s.add_argument("--dag-records", help="checkout of the DAG's `records` branch")
    s.add_argument("--env")
    s.add_argument("--commit")
    s.add_argument("--seed", type=int, required=True)
    s.add_argument("--count", type=int, default=3)
    s.add_argument("--validate", help="a manifest whose source_refs to validate")

    s = add("doctor", cmd_doctor, "check policy, schemas, records and configuration")
    s.add_argument("--base", required=True)
    s.add_argument("--records")
    s.add_argument("--repo")

    sub.add_parser("report", help="generate the learning report (ci/learning/report.py)",
                   add_help=False).set_defaults(fn=None)
    return p


def main(argv: list[str] | None = None) -> int:
    argv = list(sys.argv[1:] if argv is None else argv)
    if argv[:1] == ["report"]:
        try:
            return cmd_report(None, argv[1:])
        except CliError as e:
            emit({"error": str(e)})
            return 2
    a = parser().parse_args(argv)
    try:
        return a.fn(a)
    except (CliError, POL.PolicyError, RS.RecordError, A.ActivationError, OSError,
            ValueError, KeyError, json.JSONDecodeError) as e:
        emit({"error": f"{type(e).__name__}: {e}"[:4000]})
        return 2
    except SystemExit:
        raise


if __name__ == "__main__":
    sys.exit(main())
