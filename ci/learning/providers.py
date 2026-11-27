"""Model providers for the trusted evaluator (spec 8.1, 8.3-8.4).

`local-cli` runs one solver program per trial. The programs live in `ci/learning/solvers/`: base
branch code, chosen by name in the maintainers' policy (`profiles[].settings.solver`), never an
arbitrary path. Each trial gets a fresh empty directory, a scrubbed environment and the profile's
wall-clock limit. The program reads one request on standard input:

    {"schema": "sigaba.learning.solver-request.v1", "role", "notebook" (text), "notebook_sha256",
     "family": {"id", "lean_family", "lean_module"}, "descriptor_bits", "target" (the statement to
     prove, `SigabaNeo.Benchmark.Target <family> <bits as a Lean list>`), "budget"}

and writes one response on standard output:

    {"status": "answered" | "no_answer" | "budget_exhausted" | "timeout" | "provider_error",
     "solution": {"module_text": "<a Lean module>", "theorem": "<its theorem's full name>"} | null,
     "usage": {"model_calls", "input_tokens", "output_tokens", ..., "wall_seconds"},
     "model": "<the model the provider reported>"}

Nothing the program says is a score: the verifier (`#sigaba_task_check` in the sandbox) decides.

A trial runs only when the runner's environment says the evaluation is authorized
(`SIGABA_LEARNING_EVALUATOR=authorized`, set by maintainers in the protected `learning-evaluator`
Environment or on their own machine). This prevents an accidental paid run; without it the
provider is not authorized and the evaluator answers `awaiting_evaluator`. Never a fallback:
an unknown solver name, a missing program or a missing model CLI is `provider_error`.

Solvers:

* `scripted-fixture`: a deterministic program for the bootstrap fixture families. It answers
  only when the notebook names the right lemma, so a paired comparison between two notebooks gives
  a real, Lean-verified difference without any model. A pipeline test, not research.
* `claude-code`: runs the Claude Code CLI (`claude -p`) with the notebook and the task, and
  extracts the Lean module from its answer. Opt-in and metered by the provider: a maintainer
  enables it, with a budget.
"""

from __future__ import annotations

import json
import os
import shutil
import subprocess
import sys
import tempfile
import time
from pathlib import Path

AUTH_ENV = "SIGABA_LEARNING_EVALUATOR"
SOLVERS_DIR = Path(__file__).resolve().parent / "solvers"
SOLVERS = {"scripted-fixture": "scripted_fixture.py", "claude-code": "claude_code.py"}
# Environment variables a solver may see (the model CLI's own login lives in HOME on the
# maintainer's machine; a hosted runner passes its token through the Environment).
PASS_ENV = ("PATH", "LANG", "LC_ALL", "ANTHROPIC_API_KEY", "CLAUDE_CODE_OAUTH_TOKEN")
MAX_OUTPUT = 4 * 1024 * 1024


def lean_list(bits: str) -> str:
    return "[" + ", ".join("true" if c == "1" else "false" for c in bits) + "]"


class LocalCliProvider:
    name = "local-cli"

    def __init__(self, env: dict | None = None, home: Path | None = None):
        self.env = os.environ if env is None else env
        self.home = home

    def authorized(self, profile: dict) -> bool:
        s = profile.get("settings", {})
        return (profile.get("provider") == self.name and self.env.get(AUTH_ENV) == "authorized"
                and s.get("solver") in SOLVERS)

    def request(self, req) -> dict:
        return {"schema": "sigaba.learning.solver-request.v1", "role": req.role,
                "notebook": req.notebook.decode("utf-8", "replace"),
                "notebook_sha256": req.notebook_sha256,
                "family": {"id": req.family_id, "lean_family": req.lean_family,
                           "lean_module": req.lean_module},
                "descriptor_bits": req.descriptor_bits,
                "target": f"SigabaNeo.Benchmark.Target {req.lean_family} "
                          f"{lean_list(req.descriptor_bits)}",
                "budget": req.profile.get("budget", {})}

    def solve(self, req):
        from .evaluate import SolverResponse
        s = req.profile.get("settings", {})
        prog = SOLVERS.get(s.get("solver"))
        if prog is None or not (SOLVERS_DIR / prog).is_file():
            return SolverResponse("provider_error", None, {}, None)
        wall = int(req.profile.get("budget", {}).get("wall_seconds", 600))
        work = Path(tempfile.mkdtemp(prefix="solver-"))
        env = {k: v for k, v in self.env.items() if k in PASS_ENV}
        env["HOME"] = str(self.home) if self.home else self.env.get("HOME", str(work))
        env["SIGABA_SOLVER_SETTINGS"] = json.dumps(s, sort_keys=True)
        t0 = time.monotonic()
        try:
            p = subprocess.run([sys.executable, "-I", str(SOLVERS_DIR / prog)], cwd=work,
                               env=env, input=json.dumps(self.request(req)), text=True,
                               capture_output=True, timeout=wall)
        except subprocess.TimeoutExpired:
            return SolverResponse("timeout", None, {"model_calls": None,
                                                    "wall_seconds": wall}, None)
        finally:
            shutil.rmtree(work, ignore_errors=True)
        elapsed = int(time.monotonic() - t0)
        if p.returncode != 0 or len(p.stdout) > MAX_OUTPUT:
            return SolverResponse("provider_error", None, {"wall_seconds": elapsed}, None)
        try:
            out = json.loads(p.stdout)
        except json.JSONDecodeError:
            return SolverResponse("provider_error", None, {"wall_seconds": elapsed}, None)
        if not isinstance(out, dict):
            return SolverResponse("provider_error", None, {"wall_seconds": elapsed}, None)
        usage = out.get("usage") if isinstance(out.get("usage"), dict) else {}
        usage = {**usage, "wall_seconds": elapsed}   # measured here, not reported
        sol = out.get("solution")
        if not (isinstance(sol, dict) and isinstance(sol.get("module_text"), str) and
                isinstance(sol.get("theorem"), str)):
            sol = None
        status = out.get("status")
        if status not in ("answered", "no_answer", "budget_exhausted", "timeout",
                          "provider_error"):
            status = "provider_error"
        model = out.get("model") if isinstance(out.get("model"), str) else None
        return SolverResponse(status, sol, usage, model)
