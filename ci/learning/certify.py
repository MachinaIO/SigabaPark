"""Generator certification, run inside the sandbox image (no network, no token, no secrets).

Given `route.json` (trusted, from the precheck) and the fetched files, it

1. checks that each file's SHA-256 is the one the precheck read (the result binds to them);
2. lays out a Lake workspace requiring the core (the image's `/core`), with the generator's
   modules at `Generators.<Role>.<FamilyCamel>.<GenCamel>.V<NNNN>.Generate` / `.Certificate`;
3. builds the certificate module, then runs the core's `#sigaba_generator_check` with
   L = manifest `levels`, k = manifest `seed_bits` (equal to the family policy's) and h = the
   family policy's `entropy_bits` (never the manifest's);
4. smoke-samples a bounded number of fresh seeds (`os.urandom`, committed) per level with
   `#sigaba_generator_sample`, each descriptor confirmed by the kernel in a separate process with
   `#sigaba_generator_link` (the sampler's process runs the generator's code), and re-samples the
   first seed of each level to check determinism.

Any failure, malformed output or timeout rejects the version. A failing seed is never replaced by
another: sampling stops. Samples are runtime sanity checks only; they never establish entropy.

The output (`sigaba.learning.certify-result.v1`) is data from the sandbox: `decide.py` validates it
and binds it to the pull request before anything is recorded.
"""

from __future__ import annotations

from pathlib import Path

from . import canon, lean_iface as LI, sampling, schema

MAX_SMOKE_PER_LEVEL = 8
MAX_SMOKE_TOTAL = 64


def smoke_context(g: dict, revision: str | None) -> str:
    return (f"smoke:{g['role']}/{g['family_id']}/{g['generator_id']}/v{g['version']:04d}"
            f"@{revision or 'local'}")


def certify(route: dict, files: Path, core: Path, workdir: Path, smoke_seeds: int = 2,
            timeout: float = 1800, env: str | None = None, runner=None,
            rng: sampling.RandomSource | None = None) -> dict:
    rng = rng or sampling.RandomSource()
    g = route.get("generator") if isinstance(route, dict) else None
    gref = {k: g[k] for k in ("role", "family_id", "generator_id", "version")} if g else \
        {"role": "design", "family_id": "x", "generator_id": "x", "version": 1}
    out = {"schema": "sigaba.learning.certify-result.v1", "revision": route.get("revision"),
           "env": env, "generator": gref, "files": dict(g["files"]) if g else {},
           "build": {"ok": False, "log": ""},
           "lean_result": {"verdict": "error", "problems": []}, "smoke": [], "reveal": [],
           "problems": [], "status": "rejected"}

    def done() -> dict:
        out["problems"] = [p[:4000] for p in out["problems"][:500]]
        out["build"]["log"] = out["build"]["log"][-20000:]
        ok = (not out["problems"] and out["build"]["ok"] and
              out["lean_result"]["verdict"] == "verified" and out["smoke"] and
              all(s["status"] == "ok" for s in out["smoke"]))
        out["status"] = "certified" if ok else "rejected"
        probs = schema.check(out, "certify-result")
        if probs:
            raise AssertionError("certify output does not match its schema: " + "; ".join(probs))
        return out

    if not g or route.get("route") != "generator" or not route.get("ok"):
        out["problems"].append("the route is not an admitted generator pull request")
        return done()
    if not 1 <= smoke_seeds <= MAX_SMOKE_PER_LEVEL or smoke_seeds * g["levels"] > MAX_SMOKE_TOTAL:
        out["problems"].append("the smoke-test budget is out of bounds")
        return done()
    blobs = {}
    for path, sha in g["files"].items():
        p = Path(files) / path
        if p.is_symlink() or not p.is_file():
            out["problems"].append(f"{path}: missing")
            continue
        b = p.read_bytes()
        if canon.sha256_bytes(b) != sha:
            out["problems"].append(f"{path}: content differs from what the precheck read")
        blobs[path] = b
    if out["problems"]:
        return done()
    ws = LI.Workspace(Path(workdir), Path(core), timeout=timeout, runner=runner)
    for name, module in (("Generate.lean", g["generate_module"]),
                         ("Certificate.lean", g["certificate_module"])):
        ws.write_module(module, blobs[f"{g['dir']}/{name}"])
    ok, log, timed_out = ws.build([g["certificate_module"]])
    out["build"] = {"ok": ok, "log": LI.errors(log, 80)}
    if not ok:
        out["problems"].append("the build " + ("timed out" if timed_out else "failed"))
        return done()
    res, log, _ = ws.command([LI.COMMAND_IMPORT, g["lean_module"], g["certificate_module"]],
                             LI.check_cmd(g["certificate_module"], g["lean_family"],
                                          g["generate_decl"], g["certificate_decl"],
                                          g["levels"], g["seed_bits"], g["entropy_bits"]),
                             LI.CHECK_OUTPUT)
    out["lean_result"] = LI.parse_check(res, log)
    if out["lean_result"]["verdict"] != "verified":
        return done()
    ctx = smoke_context(g, route.get("revision"))

    def sample(level: int, seed: str) -> tuple[str | None, str]:
        bits, why, _ = LI.sample_linked(ws, g["lean_module"], g["generate_module"],
                                        g["lean_family"], g["generate_decl"], g["levels"],
                                        g["seed_bits"], level, seed, g["max_descriptor_bits"])
        if bits is not None:
            return bits, ""
        reasons.append(why)
        return None, ("timeout" if "timed out" in why or why == "timeout" else
                      "malformed" if why.startswith("malformed") else "failed")

    reasons: list[str] = []

    for level in range(g["levels"]):
        first = None
        for j in range(smoke_seeds):
            s = sampling.draw_seed(rng, g["seed_bits"], ctx)
            bits, status = sample(level, s["seed_bits"])
            out["smoke"].append({"level": level, "seed_commitment": s["seed_commitment"],
                                 "descriptor_sha256": canon.sha256_bytes(bits.encode())
                                 if bits is not None else None,
                                 "status": "ok" if bits is not None else status})
            out["reveal"].append({"pair_id": len(out["reveal"]), "family_id": g["family_id"],
                                  "generator_id": g["generator_id"], "version": g["version"],
                                  "level": level, **s, "descriptor_bits": bits})
            if bits is None:
                out["problems"].append(f"level {level}: sampling a seed {status}"
                                       f" ({reasons[-1] if reasons else status}); the version "
                                       "is rejected (no replacement seed is drawn)")
                return done()
            if j == 0:
                first = (s["seed_bits"], bits)
        again, status = sample(level, first[0])
        if again != first[1]:
            out["problems"].append(f"level {level}: the same seed gave a different descriptor "
                                   f"({status or 'mismatch'}): not deterministic")
            return done()
    return done()
