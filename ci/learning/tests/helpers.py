"""Shared offline fixtures: a temporary base checkout, fetched pull request files, certified
generators, calibration records and fake Lean runners. No network, no Lean."""

from __future__ import annotations

import copy
import json
import re
import shutil
import subprocess
import tempfile
import unittest
from pathlib import Path

from ci.learning import canon, contract as C, lean_iface as LI, records as RS

REV = "a" * 40
BASE_SHA = "b" * 40
FAM_REV = "sha256:" + "1" * 64
T0 = 1_800_000_000.0           # a fixed clock


def family(fid, role="design", group=None, assessment="training", seed_bits=16,
           entropy_bits=8, bootstrap=False):
    return {"family_id": fid, "role": role,
            "lean_module": "SigabaNeoStd.Benchmarks.Families.Test",
            "lean_family": f"SigabaNeo.Benchmark.Families.Test.{fid.replace('-', '_')}",
            "revision": FAM_REV, "group": group or f"g-{fid}", "seed_bits": seed_bits,
            "entropy_bits": entropy_bits, "max_levels": 4, "max_descriptor_bits": 4096,
            "assessment": assessment, "bootstrap": bootstrap, "approved_by": "maint"}


def policy(**over):
    p = {
        "schema": "sigaba.learning.policy.v1", "policy_id": "policy-0001",
        "epoch": {"id": "epoch-0001", "dag_snapshot": BASE_SHA, "environment_id": "env-2",
                  "core_revision": "c" * 40,
                  "strength_digest": canon.digest(None)},
        "families": [family("fam-a", bootstrap=True), family("fam-b"),
                     family("fam-r", assessment="reserved"),
                     family("fam-c", role="cryptanalysis")],
        "bootstrap_generators": [{"family_id": "fam-a", "generator_id": "gen1", "version": 1}],
        "notebooks": {"max_tokens": 100, "max_bytes": 400,
                      "tokenizer": {"kind": "proxy-bytes-div-3", "version": "1"}},
        "curriculum": {"target": "0.40", "lo": "0.20", "hi": "0.60", "min_samples": 4,
                       "exploration_fraction": "0.10", "stale_after_days": 30},
        "promotion": {"screen_pairs": 6, "confirm_pairs": 20, "alpha": "0.05",
                      "delta_ni": "0.05", "infra_retries": 1,
                      "provisional_within_family": False, "require_family_disjoint": True},
        "profiles": [{"profile_id": "profile-0001", "role": "design", "provider": "mock",
                      "model": "mock-1", "settings": {},
                      "budget": {"max_model_calls": 10, "max_input_tokens": 1000,
                                 "max_output_tokens": 1000, "wall_seconds": 100,
                                 "lean_seconds": 100}}],
        "evaluator": {"enabled": True, "provider": "mock", "max_trials_per_run": 1000}}
    for k, v in over.items():
        p[k] = v
    boot = {f["family_id"] for f in p["families"] if f["bootstrap"]}
    p["bootstrap_generators"] = [b for b in p["bootstrap_generators"] if b["family_id"] in boot]
    return p


class TempCase(unittest.TestCase):
    def setUp(self):
        self.tmp = Path(tempfile.mkdtemp(prefix="learning-test-"))
        self.addCleanup(shutil.rmtree, self.tmp, True)

    def make_base(self, pol=None, trusted=None, notebooks=None) -> Path:
        base = self.tmp / "base"
        (base / "meta").mkdir(parents=True, exist_ok=True)
        (base / "env").mkdir(parents=True, exist_ok=True)
        (base / "meta" / "trusted.json").write_text(json.dumps(
            trusted or {"mode": "collaborators", "accept": ["listed"], "automerge": []}))
        (base / "meta" / "learning.json").write_text(json.dumps(pol or policy()))
        (base / "env" / "environments.json").write_text(json.dumps(
            {"environments": [{"id": "env-2", "state": "default"}]}))
        for role, text in (notebooks or {}).items():
            (base / "notebooks").mkdir(exist_ok=True)
            (base / "notebooks" / f"{role}.md").write_bytes(text)
        self.base = base
        return base

    def set_policy(self, pol) -> None:
        (self.base / "meta" / "learning.json").write_text(json.dumps(pol))

    def make_fetched(self, rows: list[tuple], name="fetched", revision=REV) -> Path:
        """rows: (path, status, bytes|None[, extra dict])."""
        d = self.tmp / name
        shutil.rmtree(d, ignore_errors=True)
        out = []
        for row in rows:
            path, status, data = row[:3]
            extra = row[3] if len(row) > 3 else {}
            r = {"filename": path, "status": status, "type": "blob", "mode": "100644",
                 "size": len(data) if data is not None else None}
            r.update(extra)
            out.append(r)
            if data is not None:
                p = d / "files" / path
                p.parent.mkdir(parents=True, exist_ok=True)
                p.write_bytes(data)
        d.mkdir(parents=True, exist_ok=True)
        (d / "files.json").write_text(json.dumps({"revision": revision, "files": out}))
        return d


GEN_NS = "Generators.Design.FamA.Gen1.V0001"
GENERATE = f"""import SigabaNeo.Benchmark
import SigabaNeoStd.Benchmarks.Families.Test

namespace {GEN_NS}

-- a comment mentioning #eval and unsafe is fine
@[simp] def generate (d : Fin 2) (s : Fin 16 → Bool) : Nat := d.val + (if s 0 then 1 else 0)

end {GEN_NS}
"""
CERTIFICATE = f"""import {GEN_NS}.Generate
import Mathlib.Data.Nat.Basic

namespace {GEN_NS}

theorem certificate : True := trivial

end {GEN_NS}
"""


def manifest(**over):
    m = {"schema": "sigaba.generator.v1", "role": "design", "family_id": "fam-a",
         "family_revision": FAM_REV, "generator_id": "gen1", "version": 1, "parent": None,
         "seed_bits": 16, "levels": 2, "generate_decl": f"{GEN_NS}.generate",
         "certificate_decl": f"{GEN_NS}.certificate",
         "source_refs": [], "bootstrap": {"approved_by": "maint", "provenance": "std"},
         "description": "test generator"}
    m.update(over)
    return {k: v for k, v in m.items() if v is not ...}


def generator_rows(m=None, gen=GENERATE, cert=CERTIFICATE, d="generators/design/fam-a/gen1/v0001"):
    m = manifest() if m is None else m
    return [(f"{d}/manifest.json", "added", json.dumps(m).encode()),
            (f"{d}/Generate.lean", "added", gen.encode()),
            (f"{d}/Certificate.lean", "added", cert.encode())]


class FakeLean:
    """A fake `lake`: builds succeed unless told otherwise; commands write the configured JSON
    outputs into their working directory. `sample(level, seed)` gives descriptor bits."""

    def __init__(self, check=None, sample=None, build_ok=True, timeout_on=None, link=None):
        # `link(level, seed)`: what the kernel computes (by default the same as the sampler);
        # a different value models a sampler whose compiled code lies.
        self.link = link
        self.last: dict = {}
        self.check = check if check is not None else {"verdict": "certified", "problems": []}
        self.sample = sample or (lambda level, seed: f"{level:02b}" + seed)
        self.build_ok = build_ok
        self.timeout_on = timeout_on
        self.commands: list[str] = []

    def __call__(self, args, stdin, cwd, timeout):
        if args[:2] == ["lake", "build"]:
            if self.timeout_on == "build":
                return subprocess.CompletedProcess(args, 124, "", "timed out")
            return subprocess.CompletedProcess(args, 0 if self.build_ok else 1, "",
                                               "" if self.build_ok else "error: boom")
        cmd = stdin.strip().splitlines()[-1]
        self.commands.append(cmd)
        if cmd.startswith(LI.CHECK_COMMAND):
            if self.check is not None:
                (Path(cwd) / LI.CHECK_OUTPUT).write_text(json.dumps(self.check))
            return subprocess.CompletedProcess(args, 0, "", "")
        if cmd.startswith(LI.SAMPLE_COMMAND):
            if self.timeout_on == "sample":
                return subprocess.CompletedProcess(args, 124, "", "timed out")
            m = re.search(r' (\d+) "([01]+)"$', cmd)
            level, seed = int(m.group(1)), m.group(2)
            bits = self.sample(level, seed)
            self.last[(level, seed)] = bits
            if bits is not None:
                (Path(cwd) / LI.SAMPLE_OUTPUT).write_text(json.dumps(
                    {"verdict": "linked", "level": level, "seed": seed, "descriptor": bits}))
            return subprocess.CompletedProcess(args, 0, "", "")
        if cmd.startswith(LI.LINK_COMMAND):
            m = re.search(r' (\d+) "([01]+)" "([01]*)"$', cmd)
            level, seed, bits = int(m.group(1)), m.group(2), m.group(3)
            want = self.link(level, seed) if self.link else self.last.get((level, seed))
            if want == bits:
                (Path(cwd) / LI.LINK_OUTPUT).write_text(json.dumps(
                    {"verdict": "linked", "level": level, "seed": seed, "descriptor": bits}))
            else:
                (Path(cwd) / LI.LINK_OUTPUT).write_text(json.dumps(
                    {"verdict": "rejected", "problems": ["the kernel does not confirm"]}))
            return subprocess.CompletedProcess(args, 0, "", "")
        return subprocess.CompletedProcess(args, 1, "", "unknown command")


# -- records fixtures --------------------------------------------------------------------------


def certify_generator(store: RS.Store, base: Path, pol: dict, fam: str, gen: str, version=1,
                      levels=2, role="design", status="certified"):
    """A certification record plus the certified files on main."""
    d = f"generators/{role}/{fam}/{gen}/v{version:04d}"
    files = {}
    for name, text in (("manifest.json", "{}"), ("Generate.lean", f"-- {gen} {version}"),
                       ("Certificate.lean", f"-- cert {gen} {version}")):
        p = base / d / name
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(text)
        files[f"{d}/{name}"] = canon.sha256_bytes(text.encode())
    f = next(x for x in pol["families"] if x["family_id"] == fam)
    rec = {"schema": "sigaba.learning.certification.v1", "role": role, "family_id": fam,
           "family_revision": f["revision"], "generator_id": gen, "version": version, "path": d,
           "pr": 1, "head": REV, "author": "someone", "files": files,
           "seed_bits": f["seed_bits"], "levels": levels, "entropy_bits": f["entropy_bits"],
           "required_bits": f["entropy_bits"], "equivalence": None,
           "certificate_decl": "X.c", "generate_decl": "X.g",
           "lean_result": {"verdict": "verified", "problems": []}, "smoke": [],
           "status": status, "reason": "ok", "source_refs": [], "bootstrap": True}
    store.append([RS.stamp(rec, canon.now(lambda: T0), C.common(pol))])


def calibration(store: RS.Store, pol: dict, fam: str, gen: str, level: int, n: int, s: int,
                ref_sha: str, version=1, when=T0, role="design"):
    rec = {"schema": "sigaba.learning.calibration.v1", "role": role, "family_id": fam,
           "generator_id": gen, "version": version, "level": level,
           "profile_id": "profile-0001", "reference_notebook_sha256": ref_sha,
           "contract_id": "sha256:" + "9" * 64, "trial_ids": [], "n": n, "successes": s,
           "failures": {}, "infra_errors": 0, "p_hat": s / n if n else None, "ci": None,
           "usage": {k: None for k in ("model_calls", "input_tokens", "output_tokens",
                                       "reasoning_tokens", "cached_tokens", "wall_seconds",
                                       "lean_seconds")},
           "state": "fresh", "selected": False, "eligibility": "eligible"}
    store.append([RS.stamp(rec, canon.now(lambda: when), C.common(pol))])


def deepcopy(x):
    return copy.deepcopy(x)
