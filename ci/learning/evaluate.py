"""The trusted evaluation runner (spec 8): calibration, paired screen -> confirm, anchors.

Only a maintainer-authorized runner executes this (never a pull request's workflow code). It owns
the randomness, the frozen contracts, the provider and the verifier:

* Every comparison is frozen first (`contract.py`); seeds are drawn afterwards from the OS
  CSPRNG, committed, and revealed only when the contract's comparison is complete.
* Each pair gives exactly the same task (seed, descriptor) to both arms, in an order derived
  from the pair's committed seed (`sampling.run_order`); arms never share context.
* A solution scores only through the injected verifier (in production the core's
  `#sigaba_task_check` in the sandbox); a provider's own claim of success is ignored. Exceeding the
  profile's budget is `unsolved / budget_exhausted`.
* Infrastructure errors (provider or verifier failures, generation failures) are retried on the
  same frozen task up to `promotion.infra_retries` times; an unresolved one stops the run and the
  comparison is `infra_error` (not promotable). No seed is ever replaced or filtered.
* With the evaluator disabled in the policy, no profile for the role, or no authorized provider
  for it, nothing runs and the result is `awaiting_evaluator` (never a fallback provider).
* Idempotent: a contract that already has a final comparison is not run again; a re-run after
  infrastructure failures starts a full replacement run (new `run_id`), at most
  `infra_retries + 1` runs per contract.

Providers implement `Provider`. Only `MockProvider` (tests and `--dry-run`) exists here: a real
model provider must be added and authorized by a maintainer; until then evaluation is
`awaiting_evaluator`.
"""

from __future__ import annotations

import json
import time
import uuid
from dataclasses import dataclass, field
from fractions import Fraction
from pathlib import Path
from typing import Callable

from . import activation as A, canon, contract as C, curriculum as CU, decide as DE, \
    lean_iface as LI, notebooks as NB, policy as POL, records as RS, registry, sampling, stats
from .records import Store

USAGE_KEYS = ("model_calls", "input_tokens", "output_tokens", "reasoning_tokens",
              "cached_tokens", "wall_seconds", "lean_seconds")
# Usage fields a provider must measure: without them the budget cannot be enforced.
CRITICAL_USAGE = ("model_calls", "wall_seconds")
BUDGET_OF = {"model_calls": "max_model_calls", "input_tokens": "max_input_tokens",
             "output_tokens": "max_output_tokens", "wall_seconds": "wall_seconds",
             "lean_seconds": "lean_seconds"}
FORBIDDEN_IMPORT_PREFIXES = ("Generators",)


class GenerationError(Exception):
    pass


@dataclass
class SolverRequest:
    role: str
    profile: dict
    notebook: bytes
    notebook_sha256: str
    family_id: str
    lean_family: str
    lean_module: str
    descriptor_bits: str
    target: str


@dataclass
class SolverResponse:
    # answered | no_answer | budget_exhausted | timeout | provider_error
    status: str
    solution: dict | None = None      # {"module_text": str, "theorem": str}
    usage: dict = field(default_factory=dict)
    model_reported: str | None = None
    claimed_solved: bool | None = None   # ignored: only the verifier scores


class Provider:
    name = "none"

    def authorized(self, profile: dict) -> bool:
        return False

    def solve(self, req: SolverRequest) -> SolverResponse:
        raise NotImplementedError


class MockProvider(Provider):
    """A deterministic test provider. `behavior(req)` returns a `SolverResponse`."""
    name = "mock"

    def __init__(self, behavior: Callable[[SolverRequest], SolverResponse] | None = None):
        self.behavior = behavior or (lambda req: SolverResponse(
            "no_answer", None, {"model_calls": 1, "wall_seconds": 1}, "mock-1"))
        self.calls: list[SolverRequest] = []

    def authorized(self, profile: dict) -> bool:
        return profile.get("provider") == "mock"

    def solve(self, req: SolverRequest) -> SolverResponse:
        self.calls.append(req)
        return self.behavior(req)


PROVIDERS: dict[str, Callable[[], Provider]] = {}


def provider_for(pol: dict, profile: dict | None, dry_run: bool) -> tuple[Provider | None, str]:
    if dry_run:
        return MockProvider(), "dry run: mock provider, nothing is published"
    ev = pol["evaluator"]
    if not ev["enabled"]:
        return None, "the evaluator is disabled in meta/learning.json"
    if profile is None:
        return None, "no evaluation profile for this role"
    if profile["provider"] != ev["provider"]:
        return None, "the role's profile does not use the enabled provider"
    make = PROVIDERS.get(ev["provider"])
    if make is None:
        return None, f"no adapter for provider {ev['provider']!r} is installed"
    p = make()
    if not p.authorized(profile):
        return None, f"provider {ev['provider']!r} is not authorized here"
    return p, ""


class Sampler:
    def sample(self, gen: dict, level: int, seed: str) -> str:
        raise NotImplementedError


class Verifier:
    def verify(self, req: SolverRequest, solution: dict) -> dict:
        raise NotImplementedError


class LeanSampler(Sampler):
    """Descriptors through the core's `#sigaba_generator_sample` in a workspace holding the
    generator modules from `main` (run this inside the sandbox image)."""

    def __init__(self, make_ws: Callable[[str], LI.Workspace], base: Path, pol: dict):
        # One workspace per generator version: each is built once, then locked before its
        # generator code runs (lean_iface.Workspace.lock).
        self.make_ws, self.base, self.pol = make_ws, Path(base), pol
        self.wss: dict[str, LI.Workspace] = {}

    def sample(self, gen: dict, level: int, seed: str) -> str:
        fam = POL.family(self.pol, gen["family_id"])
        ns = LI.generator_namespace(gen["role"], gen["family_id"], gen["generator_id"],
                                    gen["version"])
        man = read_json(self.base / gen["path"] / "manifest.json")
        if ns not in self.wss:
            ws = self.make_ws(ns)
            for n in ("Generate", "Certificate"):
                ws.write_module(f"{ns}.{n}",
                                (self.base / gen["path"] / f"{n}.lean").read_bytes())
            ok, log, _ = ws.build([f"{ns}.Generate"])
            if not ok:
                raise GenerationError("build failed: " + LI.errors(log)[:500])
            self.wss[ns] = ws
        bits, why, _ = LI.sample_linked(self.wss[ns], fam["lean_module"], f"{ns}.Generate",
                                        fam["lean_family"], man["generate_decl"],
                                        gen["levels"], gen["seed_bits"], level, seed,
                                        fam["max_descriptor_bits"])
        if bits is None:
            raise GenerationError(why)
        return bits


class LeanTaskVerifier(Verifier):
    """Solutions through the core's `#sigaba_task_check` in a fresh workspace without any
    generator module (run inside the sandbox image)."""

    def __init__(self, make_ws: Callable[[], LI.Workspace]):
        self.make_ws = make_ws

    def verify(self, req: SolverRequest, solution: dict) -> dict:
        ws = self.make_ws()
        module = "Answers.Solution"
        text = solution.get("module_text")
        theorem = solution.get("theorem")
        if not isinstance(text, str) or not isinstance(theorem, str) or len(text) > 1 << 20:
            return {"verdict": "rejected", "theorem_sha256": None, "certified_value": None}
        ws.write_module(module, text.encode())
        ok, log, timed_out = ws.build([module])
        if not ok:
            if timed_out:
                return {"verdict": "error", "theorem_sha256": None, "certified_value": None}
            return {"verdict": "rejected", "theorem_sha256": None, "certified_value": None}
        try:
            cmd = LI.task_cmd(module, req.lean_family, req.descriptor_bits, theorem,
                              list(FORBIDDEN_IMPORT_PREFIXES))
        except ValueError:
            return {"verdict": "rejected", "theorem_sha256": None, "certified_value": None}
        res, log, rc = ws.command([LI.COMMAND_IMPORT, req.lean_module, module], cmd,
                                  LI.TASK_OUTPUT)
        if rc == 124:
            return {"verdict": "error", "theorem_sha256": None, "certified_value": None}
        return LI.parse_task(res)


def read_json(p: Path) -> dict:
    return json.loads(Path(p).read_text())


# -- the engine ------------------------------------------------------------------------------------


class Engine:
    def __init__(self, store: Store, pol: dict, provider: Provider, sampler: Sampler,
                 verifier: Verifier, rng: sampling.RandomSource | None = None,
                 clock: Callable[[], float] = time.time):
        self.store, self.pol = store, pol
        self.provider, self.sampler, self.verifier = provider, sampler, verifier
        self.rng = rng or sampling.RandomSource()
        self.clock = clock
        self.retries = pol["promotion"]["infra_retries"]
        self.common = C.common(pol)
        self.new: list[dict] = []
        self.generation_failures: list[dict] = []

    def now(self) -> str:
        return canon.now(self.clock)

    def seal(self, rec: dict) -> dict:
        r = RS.stamp(rec, self.now(), self.common)
        self.new.append(r)
        return r

    # -- one arm ---------------------------------------------------------------------------------

    def run_arm(self, *, run_id: str, con: dict, pair_id, arm: str, gen: dict, level: int,
                draw: dict, bits: str | None, notebook: bytes) -> dict:
        fam = POL.family(self.pol, gen["family_id"])
        base = {"schema": "sigaba.learning.trial.v1", "run_id": run_id,
                "contract_id": con["contract_id"], "stage": con["stage"], "pair_id": pair_id,
                "arm": arm, "role": con["role"], "family_id": gen["family_id"],
                "generator_id": gen["generator_id"], "version": gen["version"], "level": level,
                "seed_commitment": draw["seed_commitment"],
                "descriptor_sha256": canon.sha256_bytes(bits.encode()) if bits is not None
                else None, "notebook_sha256": canon.sha256_bytes(notebook)}
        if bits is None:
            t = self.now()
            return self.seal({**base, "model_reported": None, "started_at": t, "ended_at": t,
                              "outcome": "infra_error", "reason": "generation_error",
                              "check": None, "usage": empty_usage(), "retries": self.retries,
                              "certified_value": None})
        req = SolverRequest(con["role"], con["profile"], notebook, base["notebook_sha256"],
                            gen["family_id"], fam["lean_family"], fam["lean_module"], bits,
                            f"SigabaNeo.Benchmark.Target {fam['lean_family']} {bits!r}")
        retries = 0
        while True:
            started = self.now()
            outcome, reason, check, value, usage, model = self._attempt(req, con["profile"])
            if outcome != "infra_error" or retries >= self.retries:
                break
            retries += 1
        return self.seal({**base, "model_reported": model, "started_at": started,
                          "ended_at": self.now(), "outcome": outcome, "reason": reason,
                          "check": check, "usage": usage, "retries": retries,
                          "certified_value": value})

    def _attempt(self, req: SolverRequest, profile: dict):
        try:
            resp = self.provider.solve(req)
        except Exception:      # a provider failure is infrastructure, never a solver outcome
            return "infra_error", "provider_error", None, None, empty_usage(), None
        usage = norm_usage(resp.usage)
        model = (resp.model_reported or None) and str(resp.model_reported)[:256]
        if resp.status == "provider_error":
            return "infra_error", "provider_error", None, None, usage, model
        if any(usage[k] is None for k in CRITICAL_USAGE):
            return "infra_error", "provider_error", None, None, usage, model
        if resp.status == "timeout":
            return "unsolved", "solver_timeout", None, None, usage, model
        if resp.status == "budget_exhausted" or over_budget(usage, profile["budget"]):
            return "unsolved", "budget_exhausted", None, None, usage, model
        if resp.status != "answered" or not isinstance(resp.solution, dict):
            return "unsolved", "no_answer", None, None, usage, model
        try:
            v = self.verifier.verify(req, resp.solution)
        except Exception:
            v = {"verdict": "error", "theorem_sha256": None, "certified_value": None}
        check = {"verdict": v["verdict"], "theorem_sha256": v.get("theorem_sha256")}
        if v["verdict"] == "accepted":
            return "solved", "verified", check, v.get("certified_value"), usage, model
        if v["verdict"] == "wrong_target":
            return "unsolved", "wrong_target", check, None, usage, model
        if v["verdict"] == "error":
            return "infra_error", "verification_infra_error", check, None, usage, model
        return "unsolved", "invalid_proof", check, None, usage, model

    # -- tasks -----------------------------------------------------------------------------------

    def _task(self, con: dict, gen: dict, level: int) -> tuple[dict, str | None]:
        draw = sampling.draw_seed(self.rng, gen["seed_bits"], con["contract_id"])
        bits = None
        for _ in range(self.retries + 1):
            try:
                bits = self.sampler.sample(gen, level, draw["seed_bits"])
                fam = POL.family(self.pol, gen["family_id"])
                if not isinstance(bits, str) or set(bits) - {"0", "1"} or \
                        len(bits) > fam["max_descriptor_bits"]:
                    raise GenerationError("malformed descriptor")
                break
            except GenerationError as e:
                bits = None
                last = str(e)
        if bits is None:
            self.generation_failures.append({"family_id": gen["family_id"],
                                             "generator_id": gen["generator_id"],
                                             "version": gen["version"], "level": level,
                                             "seed_commitment": draw["seed_commitment"],
                                             "error": last[:500]})
        return draw, bits

    def run_pairs(self, con: dict, gens: dict, notebooks: dict[str, bytes]) -> dict:
        """Paired trials of a screen/confirm/anchor contract. `notebooks` maps the two arms
        (old first) to their bytes."""
        run_id = "run-" + uuid.UUID(bytes=self.rng.bytes(16)).hex
        old, new = list(notebooks)
        weights = CU.integer_weights(con["mixture"])
        pairs, reveal, complete = [], [], True
        for pair_id in range(con["trials_planned"]):
            m = con["mixture"][self.rng.categorical(weights)]
            gen = gens[(m["family_id"], m["generator_id"], m["version"])]
            draw, bits = self._task(con, gen, m["level"])
            reveal.append({"pair_id": pair_id, "family_id": m["family_id"],
                           "generator_id": m["generator_id"], "version": m["version"],
                           "level": m["level"], **draw, "descriptor_bits": bits})
            order = sampling.run_order(draw["seed_commitment"])
            if old == "anchor_baseline":
                order = tuple("anchor_baseline" if a == "incumbent" else "incumbent"
                              for a in order)
            got = {}
            for a in order:
                got[a] = self.run_arm(run_id=run_id, con=con, pair_id=pair_id, arm=a, gen=gen,
                                      level=m["level"], draw=draw, bits=bits,
                                      notebook=notebooks[a])
            pairs.append((got[old], got[new]))
            if any(t["outcome"] == "infra_error" for t in got.values()):
                complete = False
                break
        rev = self.seal({"schema": "sigaba.learning.reveal.v1",
                         "contract_id": con["contract_id"], "items": reveal})
        return {"run_id": run_id, "pairs": pairs, "complete": complete, "reveal": rev}

    def comparison(self, con: dict, res: dict, measures: dict, pr, head, anchor_epoch=None) \
            -> dict:
        old, new = [a["arm"] for a in con["arms"]]
        good = [(a, b) for a, b in res["pairs"]
                if "infra_error" not in (a["outcome"], b["outcome"])]
        counts = stats.paired_counts([(int(a["outcome"] == "solved"),
                                       int(b["outcome"] == "solved")) for a, b in good])
        nb = {"incumbent_bytes": measures[old]["bytes"],
              "incumbent_tokens": measures[old]["tokens"],
              "candidate_bytes": measures[new]["bytes"],
              "candidate_tokens": measures[new]["tokens"],
              "cap_tokens": self.pol["notebooks"]["max_tokens"],
              "tokenizer": dict(self.pol["notebooks"]["tokenizer"])}
        verdict, reason, b = DE.comparison_verdict(
            con["stage"], counts, con["trials_planned"], res["complete"], nb, self.pol,
            con["scope"], con["provisional"])
        if not res["complete"]:
            good = []         # an incomplete run is reported, never aggregated
            counts = stats.paired_counts([])
            b = stats.cp_union(0, 0, 0, POL.prob(self.pol["promotion"]["alpha"]))
        return self.seal({
            "schema": "sigaba.learning.comparison.v1", "role": con["role"],
            "contract_id": con["contract_id"], "stage": con["stage"], "scope": con["scope"],
            "provisional": con["provisional"],
            "incumbent_sha256": measures[old]["sha256"],
            "candidate_sha256": measures[new]["sha256"], "pr": pr, "head": head,
            "pair_refs": [[a["record_id"], b2["record_id"]] for a, b2 in good], **counts,
            "delta_hat": b["delta_hat"], "lower_bound": b["lower_bound"],
            "method": stats.METHOD, "alpha": self.pol["promotion"]["alpha"],
            "delta_ni": self.pol["promotion"]["delta_ni"], "notebook": nb,
            "usage": {"incumbent": sum_usage([a["usage"] for a, _ in res["pairs"]]),
                      "candidate": sum_usage([b2["usage"] for _, b2 in res["pairs"]])},
            "verdict": verdict, "reason": reason[:4000], "policy_id": self.pol["policy_id"],
            "epoch_id": self.pol["epoch"]["id"], "anchor_epoch": anchor_epoch})

    # -- calibration -------------------------------------------------------------------------------

    def run_calibration(self, con: dict, gens: dict, plan: list[dict], notebook: bytes) -> dict:
        run_id = "run-" + uuid.UUID(bytes=self.rng.bytes(16)).hex
        trials, reveal, complete = [], [], True
        for p in plan:
            gen = gens[(p["family_id"], p["generator_id"], p["version"])]
            for _ in range(p["trials"]):
                draw, bits = self._task(con, gen, p["level"])
                reveal.append({"pair_id": None, "family_id": p["family_id"],
                               "generator_id": p["generator_id"], "version": p["version"],
                               "level": p["level"], **draw, "descriptor_bits": bits})
                t = self.run_arm(run_id=run_id, con=con, pair_id=None, arm="reference", gen=gen,
                                 level=p["level"], draw=draw, bits=bits, notebook=notebook)
                trials.append(t)
                if t["outcome"] == "infra_error" and t["reason"] == "generation_error":
                    break         # this arm's batch is invalid; the generator needs attention
        rev = self.seal({"schema": "sigaba.learning.reveal.v1",
                         "contract_id": con["contract_id"], "items": reveal})
        return {"run_id": run_id, "trials": trials, "complete": complete, "reveal": rev}


def empty_usage() -> dict:
    return {k: None for k in USAGE_KEYS}


def norm_usage(u: dict | None) -> dict:
    out = empty_usage()
    for k in USAGE_KEYS:
        v = (u or {}).get(k)
        if isinstance(v, (int, float)) and not isinstance(v, bool) and v >= 0:
            out[k] = int(-(-v // 1))       # round up: never under-report usage
    return out


def over_budget(usage: dict, budget: dict) -> bool:
    return any(usage[k] is not None and usage[k] > budget[b] for k, b in BUDGET_OF.items())


def sum_usage(us: list[dict]) -> dict:
    out = {}
    for k in USAGE_KEYS:
        vals = [u[k] for u in us if u[k] is not None]
        out[k] = sum(vals) if vals else None
    return out


# -- orchestration ---------------------------------------------------------------------------------


def _gens(store: Store, base: Path, pol: dict, role: str) -> dict:
    return {(g["family_id"], g["generator_id"], g["version"]): g
            for g in registry.usable(store, base, pol, role)}


def plan_mixture(store: Store, base: Path, pol: dict, role: str, profile: dict,
                 reference_sha: str, assessment: tuple[str, ...], as_of: float | None = None) \
        -> tuple[dict, list[str], dict]:
    gens = _gens(store, base, pol, role)
    arms = CU.aggregate(store.read("calibration"), role, profile["profile_id"], reference_sha,
                        pol["curriculum"]["stale_after_days"], as_of)
    sel = CU.select(list(gens.values()), arms, pol)
    fams = CU.families_for(pol, role, assessment)
    mix = CU.freeze_mixture(sel, pol, fams)
    snapshot = sorted({rid for k, a in arms.items() if k[:3] in gens and k[0] in fams
                       for rid in a["record_ids"]})
    return mix, snapshot, gens


def prior_runs(store: Store, contract_id: str) -> tuple[dict | None, int]:
    """A final comparison of the contract (reused, never re-run), and the number of runs so
    far (trials or comparisons)."""
    comps = [c for c in store.read("comparison") if c["contract_id"] == contract_id]
    final = next((c for c in reversed(comps) if c["verdict"] != "infra_error"), None)
    runs = {t["run_id"] for t in store.read("trial") if t["contract_id"] == contract_id}
    return final, max(len(runs), len(comps))


def evaluate_notebook(*, store: Store, base: Path, pol: dict, route: dict, candidate: bytes,
                      provider: Provider | None, provider_note: str, sampler: Sampler,
                      verifier: Verifier, rng: sampling.RandomSource | None = None,
                      clock=time.time, as_of: float | None = None) -> dict:
    """Screen then (if promising) an independent confirmation of a notebook pull request."""
    out = {"status": "done", "verdict": None, "reason": "", "records": [], "screen": None,
           "confirm": None, "generation_failures": []}

    def finish(verdict: str, reason: str, eng: Engine | None = None) -> dict:
        out.update(verdict=verdict, reason=reason)
        if eng is not None:
            out["records"] = eng.new
            out["generation_failures"] = eng.generation_failures
        return out

    nb = route.get("notebook")
    if route.get("route") != "notebook" or not route.get("ok") or nb is None:
        return finish("inconclusive", "not an admitted notebook pull request")
    role = nb["role"]
    if canon.sha256_bytes(candidate) != nb["sha256"]:
        return finish("inconclusive", "the candidate bytes are not the ones the precheck read")
    incumbent = NB.read_active_file(base, role)
    state = A.active(store, role)
    if canon.sha256_bytes(incumbent) != nb["incumbent_sha256"] or \
            state["active"] != nb["incumbent_sha256"]:
        return finish("stale", "the active notebook changed since the precheck (or main and the "
                               "activation history disagree)")
    if NB.problems(candidate, pol):
        return finish("fail", "the candidate violates the notebook rules")
    profile = POL.profile(pol, role)
    if provider is None:
        return finish("awaiting_evaluator", provider_note)
    pr = pol["promotion"]
    need = 2 * (pr["screen_pairs"] + pr["confirm_pairs"])
    if pol["evaluator"]["max_trials_per_run"] < need:
        return finish("inconclusive", f"budget_insufficient: a screen and a confirmation need "
                                      f"{need} trials, the policy allows "
                                      f"{pol['evaluator']['max_trials_per_run']}")
    m_inc, m_cand = NB.measure(incumbent, pol), NB.measure(candidate, pol)
    measures = {"incumbent": m_inc, "candidate": m_cand}
    notebooks = {"incumbent": incumbent, "candidate": candidate}
    arms = [C.arm("incumbent", m_inc), C.arm("candidate", m_cand, route["pr"],
                                             route["revision"])]
    eng = Engine(store, pol, provider, sampler, verifier, rng, clock)
    train = ("training",)
    mix, snap, gens = plan_mixture(store, base, pol, role, profile, nb["incumbent_sha256"],
                                   train, as_of)
    if mix["status"] != "ok":
        return finish("inconclusive", "insufficient_generators: no eligible calibrated arm in "
                                      "the training families", eng)
    excluded = sorted(CU.families_for(pol, role, ("reserved", "future")))
    screen = C.freeze(C.build(stage="screen", role=role, scope="fresh_seed", provisional=False,
                              arms=arms, mixture=mix["mixture"], excluded_families=excluded,
                              trials_planned=pr["screen_pairs"], profile=profile, pol=pol,
                              calibration_snapshot=snap), eng.now(), pol)
    sc = _run_stage(eng, store, screen, gens, notebooks, measures, route)
    out["screen"] = sc
    if sc["verdict"] != "inconclusive" or not sc["reason"].startswith("screen_promising"):
        return finish(sc["verdict"] if sc["verdict"] in ("fail", "infra_error") else
                      "inconclusive", "screen: " + sc["reason"], eng)
    rmix, rsnap, rgens = plan_mixture(store, base, pol, role, profile, nb["incumbent_sha256"],
                                      ("reserved",), as_of)
    scope = DE.confirm_scope(pol, role, rmix["status"] == "ok")
    if isinstance(scope, str):
        return finish("inconclusive", "screen promising; " + scope, eng)
    scope_name, provisional = scope
    if scope_name == "family_disjoint":
        cmix, csnap, cgens = rmix, rsnap, rgens
        cexcl = sorted(CU.families_for(pol, role, ("training", "future")))
    else:
        cmix, csnap, cgens, cexcl = mix, snap, gens, excluded
    confirm = C.freeze(C.build(stage="confirm", role=role, scope=scope_name,
                               provisional=provisional, arms=arms, mixture=cmix["mixture"],
                               excluded_families=cexcl, trials_planned=pr["confirm_pairs"],
                               profile=profile, pol=pol, calibration_snapshot=csnap),
                       eng.now(), pol)
    cc = _run_stage(eng, store, confirm, cgens, notebooks, measures, route)
    out["confirm"] = cc
    return finish(cc["verdict"], "confirm: " + cc["reason"], eng)


def _run_stage(eng: Engine, store: Store, con: dict, gens: dict, notebooks: dict,
               measures: dict, route: dict, anchor_epoch: str | None = None) -> dict:
    final, runs = prior_runs(store, con["contract_id"])
    if final is not None:
        return final                       # idempotent: never re-run a decided contract
    if runs > eng.retries:
        return {"verdict": "infra_error", "reason": f"{runs} runs of this contract failed on "
                "infrastructure; no further replacement run", "record_id": None}
    if con["contract_id"] not in {c["contract_id"] for c in store.read("contract")}:
        eng.new.append(con)
    res = eng.run_pairs(con, gens, notebooks)
    return eng.comparison(con, res, measures, route.get("pr"), route.get("revision"),
                          anchor_epoch)


def calibrate(*, store: Store, base: Path, pol: dict, role: str, provider: Provider | None,
              provider_note: str, sampler: Sampler, verifier: Verifier,
              rng: sampling.RandomSource | None = None, clock=time.time,
              budget: int | None = None, as_of: float | None = None) -> dict:
    """One bounded calibration batch with the active notebook as the reference agent."""
    if provider is None:
        return {"status": "awaiting_evaluator", "reason": provider_note, "records": []}
    profile = POL.profile(pol, role)
    ref = NB.read_active_file(base, role)
    ref_sha = canon.sha256_bytes(ref)
    if A.active(store, role)["active"] != ref_sha:
        return {"status": "stale", "reason": "main and the activation history disagree",
                "records": []}
    gens = _gens(store, base, pol, role)
    if not gens:
        return {"status": "insufficient_generators", "reason": "no certified generator",
                "records": []}
    arms = CU.aggregate(store.read("calibration"), role, profile["profile_id"], ref_sha,
                        pol["curriculum"]["stale_after_days"], as_of)
    due = CU.due_arms(list(gens.values()), arms, pol)
    limit = pol["evaluator"]["max_trials_per_run"]
    if budget is not None:
        limit = min(limit, budget)
    plan, used = [], 0
    for d in due:
        if used + d["trials"] > limit:
            break
        plan.append(d)
        used += d["trials"]
    if not plan:
        return {"status": "nothing_due" if not due else "budget_insufficient",
                "reason": "", "records": []}
    eng = Engine(store, pol, provider, sampler, verifier, rng, clock)
    mixture = []
    for d in plan:       # fixed quotas per arm, written as exact weights
        w = Fraction(d["trials"], used)
        mixture.append({"family_id": d["family_id"], "generator_id": d["generator_id"],
                        "version": d["version"], "level": d["level"],
                        "weight": [w.numerator, w.denominator]})
    con = C.freeze(C.build(stage="calibration", role=role, scope="fresh_seed", provisional=False,
                           arms=[C.arm("reference", NB.measure(ref, pol))], mixture=mixture,
                           excluded_families=[], trials_planned=used, profile=profile, pol=pol,
                           calibration_snapshot=sorted(r for a in arms.values()
                                                       for r in a["record_ids"])),
                   eng.now(), pol)
    eng.new.append(con)
    res = eng.run_calibration(con, gens, plan, ref)
    batch: dict[tuple, list[dict]] = {}
    for t in res["trials"]:
        batch.setdefault((t["family_id"], t["generator_id"], t["version"], t["level"]),
                         []).append(t)
    rows = []
    for key, ts in sorted(batch.items()):
        done = [t for t in ts if t["outcome"] != "infra_error"]
        n, s = len(done), sum(1 for t in done if t["outcome"] == "solved")
        fails: dict[str, int] = {}
        for t in done:
            if t["outcome"] == "unsolved":
                fails[t["reason"]] = fails.get(t["reason"], 0) + 1
        ci = stats.wilson(s, n)
        rows.append({"schema": "sigaba.learning.calibration.v1", "role": role,
                     "family_id": key[0], "generator_id": key[1], "version": key[2],
                     "level": key[3], "profile_id": profile["profile_id"],
                     "reference_notebook_sha256": ref_sha, "contract_id": con["contract_id"],
                     "trial_ids": [t["record_id"] for t in ts], "n": n, "successes": s,
                     "failures": fails, "infra_errors": len(ts) - n,
                     "p_hat": s / n if n else None,
                     "ci": {"method": "wilson-95", "low": ci[0], "high": ci[1]} if ci else None,
                     "usage": sum_usage([t["usage"] for t in ts]), "state": "fresh"})
    # Selection and eligibility after adding this batch (derived, recorded for the report).
    t_now = clock() if as_of is None else as_of
    fake = [dict(r, created_at=canon.now(lambda: t_now), record_id="x") for r in rows]
    merged = CU.aggregate(store.read("calibration") + fake, role, profile["profile_id"], ref_sha,
                          pol["curriculum"]["stale_after_days"], t_now)
    sel = {(s["family_id"], s["generator_id"], s["version"]): s
           for s in CU.select(list(gens.values()), merged, pol)}
    for r in rows:
        s = sel[(r["family_id"], r["generator_id"], r["version"])]
        r["selected"] = s["level"] == r["level"]
        r["eligibility"] = s["eligibility"] if r["selected"] else (
            "uncalibrated" if merged[(r["family_id"], r["generator_id"], r["version"],
                                      r["level"])]["n"] < pol["curriculum"]["min_samples"]
            else "low_priority")
        eng.seal(r)
    return {"status": "done", "reason": "", "records": eng.new,
            "generation_failures": eng.generation_failures}


def anchor(*, store: Store, base: Path, pol: dict, role: str, anchor_epoch: str,
           provider: Provider | None, provider_note: str, sampler: Sampler, verifier: Verifier,
           rng: sampling.RandomSource | None = None, clock=time.time,
           as_of: float | None = None, pairs: int | None = None) -> dict:
    """The active notebook against the frozen empty-notebook baseline on fresh seeds from the
    anchor epoch's pinned mixture (the mixture of its first anchor contract, else the current
    training mixture, which is then pinned). Anchors never activate anything."""
    if provider is None:
        return {"status": "awaiting_evaluator", "reason": provider_note, "records": []}
    profile = POL.profile(pol, role)
    active_bytes = NB.read_active_file(base, role)
    if A.active(store, role)["active"] != canon.sha256_bytes(active_bytes):
        return {"status": "stale", "reason": "main and the activation history disagree",
                "records": []}
    gens = _gens(store, base, pol, role)
    pinned = None
    contracts = {c["contract_id"]: c for c in store.read("contract")}
    for c in store.read("comparison"):
        if c["stage"] == "anchor" and c["role"] == role and c["anchor_epoch"] == anchor_epoch:
            pinned = contracts.get(c["contract_id"])
            break
    if pinned is not None:
        mixture, snap = pinned["mixture"], pinned["calibration_snapshot"]
        missing = [m for m in mixture if (m["family_id"], m["generator_id"], m["version"])
                   not in gens]
        if missing:
            return {"status": "stale", "reason": "the anchor epoch's generators are no longer "
                    "usable; start a new anchor epoch", "records": []}
    else:
        mix, snap, _ = plan_mixture(store, base, pol, role, profile,
                                    canon.sha256_bytes(active_bytes), ("training",), as_of)
        if mix["status"] != "ok":
            return {"status": "insufficient_generators", "reason": "", "records": []}
        mixture = mix["mixture"]
    n = pairs or pol["promotion"]["screen_pairs"]
    m_base, m_act = NB.measure(b"", pol), NB.measure(active_bytes, pol)
    eng = Engine(store, pol, provider, sampler, verifier, rng, clock)
    con = C.freeze(C.build(stage="anchor", role=role, scope="fresh_seed", provisional=False,
                           arms=[C.arm("anchor_baseline", m_base), C.arm("incumbent", m_act)],
                           mixture=mixture, excluded_families=[], trials_planned=n,
                           profile=profile, pol=pol, calibration_snapshot=snap),
                   eng.now(), pol)
    comp = _run_stage(eng, store, con, gens, {"anchor_baseline": b"", "incumbent": active_bytes},
                      {"anchor_baseline": m_base, "incumbent": m_act}, {}, anchor_epoch)
    return {"status": "done", "comparison": comp, "records": eng.new,
            "generation_failures": eng.generation_failures}
