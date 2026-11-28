"""DAG-driven source sampling for generator development (spec section 6.1).

The corpus is the set of *verified* formal nodes of a DAG checkout in one environment, according to
the `records` branch (`<env>.jsonl`):

* a definition with an `OK` record;
* a solution with an `ACCEPTED` record (a complete proof; `SKETCH_ACCEPTED` sketches are
  excluded) of the `prove` kind;
* a theorem with an `OK` record of its statement and at least one such accepted solution.

Theorem placeholders without a complete proof, sketches, notes and nodes without records are
never sources. Each node is classified by its (theorem) statement as `design` (mentions `Spec`,
`Submission`), `cryptanalysis` (mentions `Assumption.Attack`, `HardAt`, `gain`, `Attack`) or
`shared` (both or neither): a heuristic tag that never establishes a theorem's role.

`sample` draws 2-4 roots for a role from that role's and the shared nodes with a seeded RNG
(`random.Random(seed)`, a controller choice recorded in the output): first a cluster uniformly (the
first two components of the node's name, so that a large cluster of near-duplicate lemmas does
not dominate), then a node of the cluster. Every root is a pinned reference: node id, path, DAG
commit and the SHA-256 of the file's exact bytes.
"""

from __future__ import annotations

import json
import random
import re
from pathlib import Path

from . import canon

DEF_RE = re.compile(r"dag/Definitions/Def_([A-Za-z_][A-Za-z0-9_]*)\.lean")
THM_RE = re.compile(r"dag/Theorems/Thm_([A-Za-z_][A-Za-z0-9_']*)\.lean")
SOL_RE = re.compile(r"dag/Solutions/([A-Za-z_][A-Za-z0-9_']*)/Sub_([A-Za-z0-9_]{1,64})\.lean")
DESIGN_HINTS = re.compile(r"\bSpec\b|\bSubmission\b")
CRYPT_HINTS = re.compile(r"Assumption\.Attack|\bHardAt\b|\.gain\b|\bAttack\b")
MAX_SOURCE_BYTES = 256 * 1024


def read_records(records: Path | None, env: str) -> list[dict]:
    if records is None:
        return []
    p = Path(records) / f"{env}.jsonl"
    if not p.is_file():
        return []
    out = []
    for line in p.read_text().splitlines():
        if line.strip():
            try:
                r = json.loads(line)
            except json.JSONDecodeError:
                continue
            if isinstance(r, dict):
                out.append(r)
    return out


def _classify(text: str) -> str:
    d, c = bool(DESIGN_HINTS.search(text)), bool(CRYPT_HINTS.search(text))
    return "design" if d and not c else "cryptanalysis" if c and not d else "shared"


def corpus(dag: Path, records: Path | None, env: str, commit: str) -> list[dict]:
    """The verified nodes of `dag` in environment `env`, as pinned references."""
    dag = Path(dag)
    recs = read_records(records, env)
    ok_defs = {r.get("path") for r in recs if r.get("kind") == "definition" and
               r.get("status") == "OK"}
    ok_thms = {r.get("name") for r in recs if r.get("kind") == "theorem" and
               r.get("status") == "OK"}
    accepted = [r for r in recs if r.get("kind") == "solution" and
                r.get("status") == "ACCEPTED" and r.get("proof_type", "prove") == "prove"]
    proved = {r.get("theorem") for r in accepted}
    acc_paths = {r.get("path") for r in accepted}
    nodes = []

    def add(kind: str, node_id: str, rel: str, name: str, statement: str) -> None:
        p = dag / rel
        if p.is_symlink() or not p.is_file() or p.stat().st_size > MAX_SOURCE_BYTES:
            return
        data = p.read_bytes()
        nodes.append({"node_id": node_id, "kind": kind, "path": rel, "name": name,
                      "commit": commit, "content_sha256": canon.sha256_bytes(data),
                      "role_class": _classify(statement), "bytes": len(data)})

    thm_text: dict[str, str] = {}
    for p in sorted((dag / "dag" / "Theorems").glob("Thm_*.lean")) \
            if (dag / "dag" / "Theorems").is_dir() else []:
        rel = str(p.relative_to(dag))
        meta = _meta(p)
        name = meta.get("name")
        if not THM_RE.fullmatch(rel) or not isinstance(name, str):
            continue
        text = p.read_text(errors="replace")
        thm_text[name] = text
        if name in ok_thms and name in proved:
            add("theorem", f"theorem:{name}", rel, name, text)
    for p in sorted((dag / "dag" / "Definitions").glob("Def_*.lean")) \
            if (dag / "dag" / "Definitions").is_dir() else []:
        rel = str(p.relative_to(dag))
        m = DEF_RE.fullmatch(rel)
        if m and rel in ok_defs:
            add("definition", f"definition:{m.group(1)}", rel, m.group(1),
                p.read_text(errors="replace"))
    for p in sorted((dag / "dag" / "Solutions").glob("*/Sub_*.lean")) \
            if (dag / "dag" / "Solutions").is_dir() else []:
        rel = str(p.relative_to(dag))
        m = SOL_RE.fullmatch(rel)
        if not m or rel not in acc_paths:
            continue
        theorem = _meta(p).get("theorem", "")
        add("solution", f"solution:{m.group(1)}/Sub_{m.group(2)}", rel,
            theorem if isinstance(theorem, str) else "", thm_text.get(theorem, ""))
    return nodes


def _meta(lean: Path) -> dict:
    js = lean.with_suffix(".json")
    try:
        m = json.loads(js.read_text()) if js.is_file() else {}
    except (json.JSONDecodeError, UnicodeDecodeError):
        return {}
    return m if isinstance(m, dict) else {}


def _cluster(n: dict) -> str:
    return ".".join(n["name"].split(".")[:2]) or n["node_id"]


def sample(nodes: list[dict], role: str, seed: int, count: int = 3,
           max_bytes: int = 64 * 1024) -> dict:
    if not 2 <= count <= 4:
        raise ValueError("sample 2 to 4 roots")
    pool = [n for n in nodes if n["role_class"] in (role, "shared") and n["bytes"] <= max_bytes]
    if not pool:
        return {"status": "empty_corpus", "role": role, "seed": seed, "roots": [],
                "corpus_size": len(nodes)}
    rng = random.Random(seed)
    clusters: dict[str, list[dict]] = {}
    for n in sorted(pool, key=lambda n: n["node_id"]):
        clusters.setdefault(_cluster(n), []).append(n)
    roots, keys = [], sorted(clusters)
    while len(roots) < count and keys:
        k = rng.choice(keys)
        n = rng.choice(clusters[k])
        roots.append(n)
        clusters[k].remove(n)
        if not clusters[k]:
            keys.remove(k)
    return {"status": "ok" if len(roots) >= 2 else "insufficient_corpus", "role": role,
            "seed": seed, "corpus_size": len(nodes), "pool_size": len(pool),
            "roots": [{k: n[k] for k in ("node_id", "kind", "path", "commit", "content_sha256",
                                         "role_class")} for n in roots]}


def ref_problems(refs: list[dict], nodes: list[dict]) -> list[str]:
    """Why a manifest's `source_refs` are not real, pinned, verified sources. Nodes are
    append-only, so the content at any later commit is the current one."""
    by_id = {n["node_id"]: n for n in nodes}
    probs = []
    for r in refs:
        n = by_id.get(r["node_id"])
        if n is None:
            probs.append(f"source_refs: {r['node_id']} is not a verified node of the DAG (complete "
                         "proofs, their theorems and checked definitions only)")
        elif n["content_sha256"] != r["content_sha256"]:
            probs.append(f"source_refs: {r['node_id']}: content_sha256 is not the node's")
    return probs
