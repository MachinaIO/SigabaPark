"""The core's Lean commands, in one place, and a Lake workspace to run them in.

The verification itself stays in the core (MachinaIO/SigabaNeo), which the sandbox image provides
at `/core`; this module only lays out files, runs `lake`, and reads the commands' JSON results.
Everything about the commands' syntax and output format is a constant below: adjust it here when
the core's interface changes. Anything unexpected in an output fails closed.

Commands (the core's syntax):

    #sigaba_generator_check "<module>" "<family>" "<generate>" "<certificate>" L k h
        checks that <certificate> has type `SigabaNeo.Benchmark.Certified <family> L k h <generate>`
        (closed, standard axioms only) and writes `generator-result.json`
        ({"verdict": "certified" | "rejected", "problems": [...], ...});
    #sigaba_generator_sample "<module>" "<family>" "<generate>" L k level "<seed 0/1 string>"
        evaluates `generate level seed` with a kernel-checked link to the emitted descriptor and
        writes its bits (`sample-result.json`: verdict "linked", "descriptor");
    #sigaba_task_check "<module>" "<family>" "<bits>" "<theorem>" "<forbidden prefix>"...
        checks that <theorem> in <module> proves `SigabaNeo.Benchmark.Target <family> <bits>`
        without importing a module under a forbidden prefix (`task-result.json`: verdict
        "solved", or "rejected" with problems).

The commands are `SigabaNeo.Trusted.GeneratorCheck` of the core (tested there by
python/tests/test_benchmark.py on its fixtures).

Lean runs in the sandbox (no network, no secrets). When the process runs as root with
`SIGABA_LEAN_UID` set, every Lean and Lake process runs as that user and is killed after each step,
as in the core's `dag_verify.py`.
"""

from __future__ import annotations

import json
import os
import re
import signal
import subprocess
from pathlib import Path
from typing import Callable

# -- the core's interface (configurable constants) -----------------------------------------------

# The module that provides the three commands (imported before running one).
COMMAND_IMPORT = "SigabaNeo.Trusted.GeneratorCheck"
CHECK_COMMAND = "#sigaba_generator_check"
SAMPLE_COMMAND = "#sigaba_generator_sample"
TASK_COMMAND = "#sigaba_task_check"
# Output files, written to the command's working directory.
CHECK_OUTPUT = "generator-result.json"
SAMPLE_OUTPUT = "sample-result.json"
LINK_COMMAND = "#sigaba_generator_link"
LINK_OUTPUT = "link-result.json"
TASK_OUTPUT = "task-result.json"
# generator-result.json
CHECK_VERDICT_FIELD = "verdict"
CHECK_PROBLEMS_FIELD = "problems"
CHECK_VERDICTS = ("certified", "rejected")
CHECK_PASS = "certified"
# generator-sample.json
SAMPLE_VERDICT_FIELD = "verdict"
SAMPLE_OK_VERDICTS = ("linked",)
SAMPLE_BITS_FIELD = "descriptor"
# Fields that, when present, must echo the request exactly.
SAMPLE_ECHO_FIELDS = {"level": "level", "seed": "seed"}
# task-result.json
TASK_VERDICT_FIELD = "verdict"
TASK_ACCEPTED = "solved"
TASK_WRONG_TARGET = "wrong_target"
TASK_THEOREM_HASH_FIELD = "theorem_sha256"
TASK_VALUE_FIELD = "certified_value"
# Bounds on what is read back.
MAX_OUTPUT_BYTES = 4 * 1024 * 1024
MAX_PROBLEMS = 200

# Module roots a generator file may import: the core (except its platform commands, which write
# files), std, Mathlib and its dependencies, Cslib. A certificate may also import its own
# generator module.
IMPORT_ROOTS = ("Init", "Std", "Mathlib", "Batteries", "Aesop", "Qq", "Plausible", "Cslib",
                "CslibFrontier", "SigabaNeoStd", "SigabaNeo")
IMPORT_DENIED = ("SigabaNeo.Platform",)
LIB = "Generators"


def lean_str(s: str) -> str:
    """A Lean string literal (only for strings this package validated: names, bit strings)."""
    if not re.fullmatch(r"[A-Za-z0-9_.'\- ]*", s):
        raise ValueError(f"refusing to quote {s!r}")
    return '"' + s + '"'


def camel(ident: str) -> str:
    """`avoid-word` -> `AvoidWord`; a leading digit gets the prefix `X` (Lean names cannot start
    with one). Identifiers with `--` or a trailing `-` are rejected by `route`, so this is
    injective on the identifiers it is given."""
    out = "".join(p[:1].upper() + p[1:] for p in ident.split("-"))
    return ("X" + out) if out[:1].isdigit() else out


def generator_namespace(role: str, family_id: str, generator_id: str, version: int) -> str:
    return f"{LIB}.{camel(role)}.{camel(family_id)}.{camel(generator_id)}.V{version:04d}"


def module_path(module: str) -> str:
    return module.replace(".", "/") + ".lean"


# -- running Lean ----------------------------------------------------------------------------------

Runner = Callable[[list, "str | None", Path, float], subprocess.CompletedProcess]


def errors(log: str, n: int = 40) -> str:
    lines = [l for l in log.splitlines() if l.startswith("error") and "build failed" not in l]
    return "\n".join(lines[:n]) if lines else "\n".join(log.splitlines()[-n:])


class Workspace:
    """A Lake project (`Generators` library at its root) that requires the core and links the
    core's built packages, so it never fetches or rebuilds Mathlib. `runner` replaces process
    execution (tests)."""

    def __init__(self, d: Path, core: Path, timeout: float = 1800, runner: Runner | None = None,
                 libs: tuple[str, ...] = (LIB,)):
        self.dir, self.core, self.timeout = Path(d), Path(core), timeout
        self.runner = runner
        self.calls = 0
        uid = os.environ.get("SIGABA_LEAN_UID")
        self.uid = int(uid) if uid and hasattr(os, "geteuid") and os.geteuid() == 0 else None
        self.dir.mkdir(parents=True, exist_ok=True)
        (self.dir / "lakefile.toml").write_text(
            'name = "learning"\nleanOptions = { autoImplicit = false }\n\n'
            f'[[require]]\nname = "SigabaNeo"\npath = {json.dumps(str(self.core))}\n' +
            "".join(f'\n[[lean_lib]]\nname = "{lib}"\n' for lib in libs))
        if runner is None:
            m = json.loads((self.core / "lake-manifest.json").read_text())
            m.update(name="learning", packages=[
                {"type": "path", "scope": "", "name": "SigabaNeo",
                 "manifestFile": "lake-manifest.json", "inherited": False,
                 "dir": str(self.core), "configFile": "lakefile.toml"},
                *[dict(p, inherited=True) for p in m["packages"]]])
            (self.dir / "lake-manifest.json").write_text(json.dumps(m, indent=1) + "\n")
            (self.dir / "lean-toolchain").write_text((self.core / "lean-toolchain").read_text())
            (self.dir / ".lake" / "packages").mkdir(parents=True, exist_ok=True)
            for p in (self.core / ".lake" / "packages").iterdir():
                if not (dst := self.dir / ".lake" / "packages" / p.name).exists():
                    dst.symlink_to(p.resolve())
        (self.dir / ".lake" / "out").mkdir(parents=True, exist_ok=True)
        if self.uid is not None:     # Lean may create its build outputs, not touch the sources
            os.chmod(self.dir / ".lake", 0o1777)
            os.chmod(self.dir / ".lake" / "out", 0o1777)

    def write_module(self, module: str, data: bytes) -> None:
        p = self.dir / module_path(module)
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_bytes(data)

    def run(self, args: list[str], stdin: str | None = None, cwd: Path | None = None,
            extra_env: dict | None = None):
        cwd = cwd or self.dir
        if self.runner is not None:
            return self.runner(args, stdin, cwd, self.timeout)
        env = {k: v for k, v in os.environ.items()
               if k not in ("LEAN_PATH", "LEAN_SRC_PATH", "SIGABA_LEAN_UID")}
        env.update(extra_env or {})
        user = {} if self.uid is None else {"user": self.uid, "group": self.uid,
                                             "extra_groups": []}
        p = subprocess.Popen(args, cwd=cwd, env=env, text=True, stdin=subprocess.PIPE,
                             stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                             start_new_session=True, **user)
        try:
            out, err = p.communicate(stdin, timeout=self.timeout)
            return subprocess.CompletedProcess(args, p.returncode, out, err)
        except subprocess.TimeoutExpired:
            self._kill(p)
            try:
                p.communicate(timeout=30)
            except subprocess.TimeoutExpired:
                pass
            return subprocess.CompletedProcess(args, 124, "",
                                               f"error: timed out after {self.timeout}s")
        finally:
            if self.uid is not None:
                self._kill(None)

    def _kill(self, p) -> None:
        if self.uid is not None:
            subprocess.run(["sh", "-c", "kill -9 -1 2>/dev/null; true"], user=self.uid,
                           group=self.uid, extra_groups=[], timeout=30)
        elif p is not None:
            try:
                os.killpg(p.pid, signal.SIGKILL)
            except (ProcessLookupError, PermissionError):
                pass

    def build(self, modules: list[str]) -> tuple[bool, str, bool]:
        """(ok, log, timed_out). A workspace is built once: then `lock` makes its build outputs
        immutable for Lean's user, and records the module search path."""
        if self.locked:
            raise RuntimeError("the workspace is locked: build everything before running code")
        r = self.run(["lake", "build", *modules])
        log = (r.stdout or "") + (r.stderr or "")
        ok = r.returncode == 0
        if ok:
            self.lock()
        return ok, log, r.returncode == 124

    locked = False
    lean_path: str | None = None

    def lock(self) -> None:
        """After the build and before any generator code runs (the sample command runs the
        generator's compiled code as Lean's user): the workspace's `.lake` becomes root's and read
        only for that user, except the per-call output directories, and the module search path is
        fixed now, so that nothing written later can change what the trusted commands load."""
        self.locked = True
        if self.runner is not None:
            return
        r = self.run(["lake", "env", "printenv", "LEAN_PATH"])
        if r.returncode == 0 and r.stdout.strip():
            self.lean_path = r.stdout.strip()
        if self.uid is not None:
            lake = self.dir / ".lake"
            for p in [lake, *lake.rglob("*")]:
                if p.is_symlink() or (self.dir / ".lake" / "out") in (p, *p.parents):
                    continue
                os.chown(p, 0, 0)
                os.chmod(p, p.stat().st_mode & ~0o022 & ~0o1000)

    def _lean_args(self) -> tuple[list[str], dict | None]:
        if self.lean_path:
            return ["lean", "--stdin"], {"LEAN_PATH": self.lean_path}
        return ["lake", "-d", str(self.dir), "env", "lean", "--stdin"], None

    def command(self, imports: list[str], cmd: str, out_name: str,
                trusted: bool = True) -> tuple[dict | None, str, int]:
        """Run one core command and read its JSON output file. The result counts only after a
        normal exit and when the file exists, is small and is a JSON object.

        Trusted commands (check, link, task check: no generator code runs in them) run from the
        workspace's root, which the core needs to tell the workspace's modules apart (it replays
        them in the kernel); their output file is created beforehand for Lean's user, in a
        directory it cannot otherwise write. The sample command (`trusted=False`) runs the
        generator's compiled code, so it runs in a fresh output directory and its output is only
        a claim, which the link command confirms in a separate process."""
        if trusted:
            f = self.dir / out_name
            if f.exists() or f.is_symlink():
                f.unlink()
            f.write_text("")
            if self.uid is not None:
                os.chown(f, self.uid, self.uid)
            text = "".join(f"import {i}\n" for i in imports) + cmd + "\n"
            args, env = self._lean_args()
            r = self.run(args, stdin=text, cwd=self.dir, extra_env=env)
            try:
                return self._read(f, r)
            finally:
                if f.exists() or f.is_symlink():
                    f.unlink()
        while True:          # a fresh directory, even in a reused workspace
            self.calls += 1
            out_dir = self.dir / ".lake" / "out" / f"call-{self.calls:05d}"
            try:
                out_dir.mkdir(parents=True, exist_ok=False)
                break
            except FileExistsError:
                continue
        if self.uid is not None:
            os.chmod(out_dir, 0o1777)
        text = "".join(f"import {i}\n" for i in imports) + cmd + "\n"
        args, env = self._lean_args()
        r = self.run(args, stdin=text, cwd=out_dir, extra_env=env)
        return self._read(out_dir / out_name, r)

    def _read(self, f: Path, r) -> tuple[dict | None, str, int]:
        log = (r.stdout or "") + (r.stderr or "")
        if r.returncode != 0 or not f.is_file() or f.is_symlink():
            return None, log, r.returncode
        if f.stat().st_size > MAX_OUTPUT_BYTES:
            return None, log + "\noutput too large", r.returncode
        try:
            data = json.loads(f.read_text())
        except (UnicodeDecodeError, json.JSONDecodeError) as e:
            return None, log + f"\noutput is not JSON: {e}", r.returncode
        if not isinstance(data, dict):
            return None, log + "\noutput is not a JSON object", r.returncode
        return data, log, r.returncode


# -- the three commands ------------------------------------------------------------------------


def check_cmd(module: str, family: str, generate: str, certificate: str, levels: int, k: int,
              h: int) -> str:
    return (f"{CHECK_COMMAND} {lean_str(module)} {lean_str(family)} {lean_str(generate)} "
            f"{lean_str(certificate)} {int(levels)} {int(k)} {int(h)}")


def sample_cmd(module: str, family: str, generate: str, levels: int, k: int, level: int,
               seed: str) -> str:
    if not re.fullmatch(r"[01]+", seed) or len(seed) != k:
        raise ValueError("the seed must be exactly k bits")
    return (f"{SAMPLE_COMMAND} {lean_str(module)} {lean_str(family)} {lean_str(generate)} "
            f"{int(levels)} {int(k)} {int(level)} {lean_str(seed)}")


def link_cmd(module: str, family: str, generate: str, levels: int, k: int, level: int,
             seed: str, bits: str) -> str:
    if not re.fullmatch(r"[01]+", seed) or len(seed) != k:
        raise ValueError("the seed must be exactly k bits")
    if not re.fullmatch(r"[01]*", bits):
        raise ValueError("descriptor bits must be a 0/1 string")
    return (f"{LINK_COMMAND} {lean_str(module)} {lean_str(family)} {lean_str(generate)} "
            f"{int(levels)} {int(k)} {int(level)} {lean_str(seed)} {lean_str(bits)}")


def sample_linked(ws: "Workspace", lean_module: str, module: str, family: str, generate: str,
                  levels: int, k: int, level: int, seed: str,
                  max_bits: int) -> tuple[str | None, str, int]:
    """(descriptor bits, why, exit status): the sampler's output (untrusted: the generator's
    code ran in that process) confirmed by the kernel in a separate link process."""
    imports = [COMMAND_IMPORT, lean_module, module]
    res, log, rc = ws.command(imports, sample_cmd(module, family, generate, levels, k, level,
                                                  seed), SAMPLE_OUTPUT, trusted=False)
    if rc == 124:
        return None, "timeout", rc
    claimed, why = parse_sample(res, level, seed, max_bits)
    if claimed is None:
        return None, ("failed: " if res is None else "malformed: ") + why, rc
    res, log, rc = ws.command(imports, link_cmd(module, family, generate, levels, k, level,
                                                seed, claimed), LINK_OUTPUT)
    if rc == 124:
        return None, "the link timed out", rc
    bits, why = parse_sample(res, level, seed, max_bits)
    if bits is None or bits != claimed:
        return None, "the kernel did not confirm the sampled descriptor" + \
            (f" ({why})" if why else ""), rc
    return bits, "", rc


def task_cmd(module: str, family: str, bits: str, theorem: str, forbidden: list[str]) -> str:
    if not re.fullmatch(r"[01]*", bits):
        raise ValueError("descriptor bits must be a 0/1 string")
    return (f"{TASK_COMMAND} {lean_str(module)} {lean_str(family)} {lean_str(bits)} "
            f"{lean_str(theorem)}" + "".join(f" {lean_str(f)}" for f in forbidden))


def parse_check(out: dict | None, log: str) -> dict:
    """`{"verdict": "verified"|"rejected"|"error", "problems": [...]}` from the check's output."""
    if out is None:
        return {"verdict": "error", "problems": ["the generator check produced no result: " +
                                                 errors(log)[:3000]]}
    v = out.get(CHECK_VERDICT_FIELD)
    probs = out.get(CHECK_PROBLEMS_FIELD, [])
    if v not in CHECK_VERDICTS or not isinstance(probs, list) or \
            not all(isinstance(p, str) for p in probs):
        return {"verdict": "error", "problems": ["the generator check's output has an "
                                                 "unexpected shape"]}
    probs = [p[:4000] for p in probs[:MAX_PROBLEMS]]
    v = "verified" if v == CHECK_PASS else v      # this package's internal name
    if v == "verified" and probs:
        return {"verdict": "error", "problems": ["the check says verified but lists problems"] +
                probs}
    return {"verdict": v, "problems": probs}


def parse_sample(out: dict | None, level: int, seed: str, max_bits: int) -> tuple[str | None, str]:
    """(descriptor bits, '') or (None, why)."""
    if out is None:
        return None, "no result"
    if out.get(SAMPLE_VERDICT_FIELD) not in SAMPLE_OK_VERDICTS:
        return None, f"verdict {str(out.get(SAMPLE_VERDICT_FIELD))[:100]!r}"
    want = {"level": level, "seed": seed}
    for k, field in SAMPLE_ECHO_FIELDS.items():
        if field in out and out[field] != want[k]:
            return None, f"the output's {field} does not echo the request"
    bits = out.get(SAMPLE_BITS_FIELD)
    if not isinstance(bits, str) or not re.fullmatch(r"[01]*", bits):
        return None, "descriptor bits are not a 0/1 string"
    if len(bits) > max_bits:
        return None, f"descriptor has {len(bits)} bits, above the family's {max_bits}"
    return bits, ""


def parse_task(out: dict | None) -> dict:
    """`{"verdict": accepted|rejected|wrong_target|error, "theorem_sha256", "certified_value"}`."""
    if out is None:
        return {"verdict": "error", "theorem_sha256": None, "certified_value": None}
    v = out.get(TASK_VERDICT_FIELD)
    th = out.get(TASK_THEOREM_HASH_FIELD)
    if isinstance(th, str) and re.fullmatch(r"[0-9a-f]{64}", th):
        th = "sha256:" + th
    if not (isinstance(th, str) and re.fullmatch(r"sha256:[0-9a-f]{64}", th)):
        th = None
    val = out.get(TASK_VALUE_FIELD)
    if not (isinstance(val, dict) and val.get("kind") in ("N", "c") and
            isinstance(val.get("value"), int) and not isinstance(val.get("value"), bool)):
        val = None
    if v == TASK_ACCEPTED:
        return {"verdict": "accepted", "theorem_sha256": th, "certified_value": val}
    if v == TASK_WRONG_TARGET:
        return {"verdict": "wrong_target", "theorem_sha256": th, "certified_value": None}
    return {"verdict": "rejected", "theorem_sha256": th, "certified_value": None}
