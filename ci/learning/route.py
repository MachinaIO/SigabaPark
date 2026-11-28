"""The learning precheck: route a pull request without running any of its code.

Input: the base checkout (`main`, trusted) and the fetched changed files (`fetch.py`: files.json and
files/). Output (`sigaba.learning.route.v1`):

* `rejected` - the author is not admitted (checked first, exactly as the core's
  `dag_tools.precheck`: `meta/trusted.json` mode `collaborators` admits GitHub permissions admin,
  maintain and write, plus the `accept` list); or the pull request touches a maintainer-only
  path (anything outside `dag/`, `generators/`, `notebooks/`: `ci/`, `.github/`, `meta/`, `env/`,
  `lakefile.toml`, `lean-toolchain`, ...), mixes kinds, deletes or renames learning files, or fails
  a generator/notebook rule. Only an admin bypass merges a maintainer-only change.
* `skipped` - a draft (admitted author): nothing is checked or run.
* `math` - only `dag/` paths: the ordinary gate decides; this check passes trivially.
* `generator` - exactly one new immutable version directory
  `generators/<role>/<family>/<generator>/vNNNN/` with `manifest.json`, `Generate.lean` and
  `Certificate.lean`, nothing else; the family approved for the role in `meta/learning.json`;
  version = previous + 1 with the matching `parent`; Lean files restricted (imports, commands,
  attributes, options). Certification follows in the sandbox (`certify.py`).
* `notebook` - exactly one of `notebooks/design.md`, `notebooks/cryptanalysis.md` added or
  modified, UTF-8, within the byte and (proxy) token caps. Evaluation follows (`evaluate.py`).
"""

from __future__ import annotations

import json
import re
from pathlib import Path

from . import canon, lean_iface as LI, notebooks as NB, policy as POL, schema, sources

WRITERS = ("admin", "maintain", "write")
IDENT = re.compile(r"[a-z0-9](?:[a-z0-9]|-(?=[a-z0-9])){0,62}")
GEN_FILE = re.compile(r"generators/(design|cryptanalysis)/([^/]+)/([^/]+)/v([0-9]{4})/"
                      r"(manifest\.json|Generate\.lean|Certificate\.lean)")
GEN_NAMES = ("manifest.json", "Generate.lean", "Certificate.lean")
LIMITS = {"manifest.json": 16 * 1024, "Generate.lean": 256 * 1024,
          "Certificate.lean": 256 * 1024}
MAX_ROWS = 5000

# -- Lean source restrictions --------------------------------------------------------------------

FORBIDDEN_WORDS = ("unsafe", "implemented_by", "extern", "run_cmd", "run_elab",
                   "run_meta", "elab", "elab_rules", "macro", "macro_rules", "syntax",
                   "declare_syntax_cat", "initialize", "builtin_initialize", "native_decide",
                   "axiom", "sorry", "admit", "ofReduceBool", "ofReduceNat", "trustCompiler",
                   "decide!", "debug_assert")
NOTATION_CMDS = ("notation", "infix", "infixl", "infixr", "prefix", "postfix")
ALLOWED_ATTRS = ("simp", "reducible", "irreducible", "semireducible", "inline", "noinline",
                 "specialize", "ext", "instance", "simps", "csimp", "refl", "symm", "trans",
                 "congr", "gcongr", "mono", "norm_cast", "push_cast", "induction_eliminator",
                 "cases_eliminator", "deprecated", "nolint", "match_pattern", "coe", "grind",
                 "fun_prop", "expose", "default_instance")
OPTION_DENIED = re.compile(r"(debug|trust|compiler|interpreter|bootstrap)(\.|$)|.*trust.*")


def strip_comments(text: str) -> str:
    """The text with comments replaced by spaces; string and character literals are kept (and
    respected, so that `--` in a string does not start a comment)."""
    out, i, n = [], 0, len(text)
    while i < n:
        c = text[i]
        if text.startswith("--", i):
            j = text.find("\n", i)
            j = n if j < 0 else j
            out.append(" " * (j - i))
            i = j
        elif text.startswith("/-", i):
            depth, j = 1, i + 2
            while j < n and depth:
                if text.startswith("/-", j):
                    depth, j = depth + 1, j + 2
                elif text.startswith("-/", j):
                    depth, j = depth - 1, j + 2
                else:
                    j += 1
            out.append(re.sub(r"[^\n]", " ", text[i:j]))
            i = j
        elif c == '"':
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == "\\" else 1
            out.append(text[i:j + 1])
            i = j + 1
        elif c == "r" and re.match(r'r#*"', text[i:]) and (i == 0 or not _ident(text[i - 1])):
            hashes = re.match(r'r(#*)"', text[i:]).group(1)
            end = text.find('"' + hashes, i + 2 + len(hashes))
            j = n if end < 0 else end + 1 + len(hashes)
            out.append(text[i:j])
            i = j
        elif c == "'" and (i == 0 or not _ident(text[i - 1])) and \
                (m := re.match(r"'(\\[^']{1,8}|[^'\\])'", text[i:])):
            out.append(m.group(0))
            i += len(m.group(0))
        else:
            out.append(c)
            i += 1
    return "".join(out)


def _ident(c: str) -> bool:
    return c.isalnum() or c in "_'!?."


def header_imports(code: str) -> tuple[list[str], list[str]]:
    """(imports, problems) of a comment-stripped Lean file: its header is `module`, `prelude` and
    `[public] [meta] import [all] M` tokens; any later `import` is a problem."""
    toks = code.split()
    imports, probs, i = [], [], 0
    while i < len(toks):
        t = toks[i]
        if t in ("module", "public", "meta", "private"):
            i += 1
        elif t == "prelude":
            probs.append("`prelude` is not allowed")
            i += 1
        elif t == "import":
            i += 1
            if i < len(toks) and toks[i] == "all":
                i += 1
            if i < len(toks):
                imports.append(toks[i])
            i += 1
        else:
            break
    if re.search(r"(?m)^\s*(public\s+|meta\s+)*import\b", " ".join(toks[i:])):
        probs.append("`import` after the header")
    return imports, probs


def lean_problems(text: str, allowed_extra: tuple[str, ...] = ()) -> list[str]:
    """Why a generator Lean file is not acceptable (before any Lean runs)."""
    code = strip_comments(text)
    imports, probs = header_imports(code)
    for m in imports:
        if m in allowed_extra:
            continue
        if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*(\.[A-Za-z_][A-Za-z0-9_']*)*", m):
            probs.append(f"import {m}: not a module name")
        elif m.split(".")[0] not in LI.IMPORT_ROOTS or \
                any(m == d or m.startswith(d + ".") for d in LI.IMPORT_DENIED) or m == "SigabaNeo":
            probs.append(f"import {m}: not allowed (the core's SigabaNeo.* except "
                         "SigabaNeo.Platform*, and " +
                         ", ".join(r for r in LI.IMPORT_ROOTS if r != "SigabaNeo")
                         + (f", or {', '.join(allowed_extra)}" if allowed_extra else "") + ")")
    for w in FORBIDDEN_WORDS:
        if re.search(rf"(?<![A-Za-z0-9_'.]){re.escape(w)}(?![A-Za-z0-9_'!?])", code):
            probs.append(f"`{w}` is not allowed in a generator")
    for w in NOTATION_CMDS:
        if re.search(rf"(?m)^\s*(@\[[^\]]*\]\s*)?((local|scoped)\s+)?{w}\b", code):
            probs.append(f"`{w}` (a syntax extension) is not allowed in a generator")
    if m := re.search(r"#[A-Za-z_][A-Za-z0-9_]*(?!\[)", code):
        probs.append(f"`{m.group(0)}` commands are not allowed in a generator")
    for m in re.finditer(r"set_option\s+([A-Za-z0-9_.]+)", code):
        if OPTION_DENIED.fullmatch(m.group(1)) or OPTION_DENIED.match(m.group(1)):
            probs.append(f"set_option {m.group(1)}: not allowed")
    for m in re.finditer(r"@\[([^\]]*)\]|\battribute\s*\[([^\]]*)\]", code):
        body = m.group(1) if m.group(1) is not None else m.group(2)
        for part in _split_attrs(body):
            words = part.split()
            while words and words[0] in ("local", "scoped"):
                words = words[1:]
            name = words[0].lstrip("-") if words else ""
            if name not in ALLOWED_ATTRS:
                probs.append(f"attribute `{part.strip()[:60]}` is not allowed in a generator "
                             f"(allowed: {', '.join(ALLOWED_ATTRS)})")
    return sorted(set(probs), key=probs.index)


def _split_attrs(body: str) -> list[str]:
    parts, depth, cur = [], 0, ""
    for c in body:
        if c in "([{":
            depth += 1
        elif c in ")]}":
            depth -= 1
        if c == "," and depth == 0:
            parts.append(cur)
            cur = ""
        else:
            cur += c
    parts.append(cur)
    return [p for p in parts if p.strip()]


# -- routing -------------------------------------------------------------------------------------


def admission(base: Path, author: str, permission: str | None) -> tuple[bool, list[str]]:
    p = Path(base) / "meta" / "trusted.json"
    trusted = json.loads(p.read_text()) if p.exists() else {"mode": "allowlist", "accept": []}
    mode = trusted.get("mode")
    writer = mode == "collaborators" and permission in WRITERS
    if mode == "open" or writer or author in trusted.get("accept", []):
        return True, []
    why = (f"@{author} has no write access to this repository (permission "
           f"{permission or 'unknown'})" if mode == "collaborators"
           else f"@{author} may not submit to this DAG yet")
    return False, [f"{why} (meta/trusted.json); nothing of the pull request was read or run"]


def _result(route: str, *, accepted=True, problems=(), revision=None, author="", permission="",
            pr=None, event="", draft=False, policy_sha=None, generator=None, notebook=None) -> dict:
    ok = route in ("math", "generator", "notebook") and not problems
    out = {"schema": "sigaba.learning.route.v1", "route": route if not problems else "rejected",
           "ok": ok, "accepted": accepted, "evaluate": ok and route == "notebook",
           "problems": [p[:4000] for p in list(problems)[:500]], "revision": revision,
           "author": author, "permission": (permission or "")[:32], "pr": pr,
           "event": (event or "")[:64], "draft": draft, "policy_sha256": policy_sha,
           "generator": generator if ok else None, "notebook": notebook if ok else None}
    if route in ("rejected", "skipped") and not problems:
        out["route"] = route
    probs = schema.check(out, "route")
    if probs:
        raise AssertionError("route output does not match its schema: " + "; ".join(probs))
    return out


def route(base: Path, fetched: Path, author: str, permission: str | None, draft: bool = False,
          event: str = "pull_request_target", pr: int | None = None,
          records: Path | None = None) -> dict:
    base, fetched = Path(base), Path(fetched)
    common = dict(author=author, permission=permission or "", pr=pr, event=event, draft=draft)
    ok, why = admission(base, author, permission)
    if not ok:
        return _result("rejected", accepted=False, problems=why, **common)
    if draft:
        return _result("skipped", **common)
    try:
        listing = json.loads((fetched / "files.json").read_text())
        rows = listing["files"]
        revision = listing.get("revision")
        if not re.fullmatch(r"[0-9a-f]{40}", revision or "") or not isinstance(rows, list):
            raise ValueError("bad listing")
    except (OSError, ValueError, KeyError, TypeError) as e:
        return _result("rejected", problems=[f"the changed files could not be read: {e}"],
                       **common)
    common["revision"] = revision
    if not rows:
        return _result("rejected", problems=["the pull request changes nothing"], **common)
    if len(rows) > MAX_ROWS:
        return _result("rejected", problems=[f"more than {MAX_ROWS} changed files"], **common)
    kinds = {}
    for r in rows:
        f = str(r.get("filename", ""))
        prev = r.get("previous_filename")
        paths = [f] + ([str(prev)] if prev else [])
        if all(p.startswith("dag/") for p in paths):
            k = "math"
        elif all(p.startswith("generators/") for p in paths):
            k = "generator"
        elif all(p.startswith("notebooks/") for p in paths):
            k = "notebook"
        else:
            k = "maintainer"
        kinds.setdefault(k, []).append(r)
    if set(kinds) == {"math"}:
        return _result("math", **common)
    # A merge group combines pull requests that each passed their own checks: its mathematical
    # nodes are the gate's, and only the learning files are routed here.
    if event == "merge_group" and "math" in kinds and len(kinds) > 1:
        nodes = kinds.pop("math")
        rows = [r for r in rows if r not in nodes]
    if "maintainer" in kinds:
        names = sorted({str(r.get("filename")) for r in kinds["maintainer"]})
        return _result("rejected", problems=[
            f"{f}: a maintainer-only path (only dag/, generators/ and notebooks/ may change in a "
            "pull request; CI, workflows, meta/, env/ and Lake configuration change only by an "
            "admin bypass)" for f in names[:100]], **common)
    if len(kinds) > 1:
        return _result("rejected", problems=[
            "a pull request may change only one of: mathematical nodes (dag/), one generator "
            f"version (generators/), one notebook (notebooks/); this one changes {sorted(kinds)}"],
            **common)
    try:
        pol = POL.load_base(base)
    except POL.PolicyError as e:
        return _result("rejected", problems=[f"the learning policy is not usable: {e}"], **common)
    common["policy_sha"] = POL.sha256(pol)
    if "generator" in kinds:
        info, probs = generator_route(base, fetched, rows, pol, records)
        return _result("generator", problems=probs, generator=info, **common)
    info, probs = notebook_route(base, fetched, rows, pol)
    out = _result("notebook", problems=probs, notebook=info, **common)
    # `evaluate`: whether the trusted evaluator should run (and ask for its Environment's
    # approval) at all. With the evaluator disabled the decision is `awaiting_evaluator` at once.
    out["evaluate"] = bool(out["evaluate"] and pol["evaluator"]["enabled"])
    return out


def _regular(r: dict) -> str | None:
    if r.get("type") != "blob" or r.get("mode") not in ("100644", "100755"):
        return (f"{r.get('filename')}: not a regular file in the commit (type {r.get('type')}, "
                f"mode {r.get('mode')}); symbolic links and submodules are not allowed")
    return None


def generator_route(base: Path, fetched: Path, rows: list[dict], pol: dict,
                    records: Path | None) -> tuple[dict | None, list[str]]:
    probs = []
    for r in rows:
        if r.get("status") != "added":
            probs.append(f"{r.get('filename')}: {r.get('status')}; generator versions are "
                         "immutable (a new version is a new directory)")
    if probs:
        return None, probs
    dirs = {}
    for r in rows:
        f = r["filename"]
        m = GEN_FILE.fullmatch(f)
        if not m:
            probs.append(f"{f}: not a generator file (generators/<role>/<family>/<generator>/"
                         "vNNNN/{manifest.json,Generate.lean,Certificate.lean})")
            continue
        for ident in (m.group(2), m.group(3)):
            if not IDENT.fullmatch(ident):
                probs.append(f"{f}: `{ident}` is not a safe identifier ([a-z0-9], single inner "
                             "hyphens, at most 63 characters)")
        dirs.setdefault(f.rsplit("/", 1)[0], []).append((r, m))
        if p := _regular(r):
            probs.append(p)
    if probs:
        return None, probs
    if len(dirs) != 1:
        return None, [f"a generator pull request adds exactly one version directory, not "
                      f"{sorted(dirs)}"]
    (vdir, items), = dirs.items()
    names = sorted(m.group(5) for _, m in items)
    if names != sorted(GEN_NAMES):
        return None, [f"{vdir}: must contain exactly manifest.json, Generate.lean and "
                      f"Certificate.lean (found {names})"]
    _, m0 = items[0]
    role, family_id, generator_id, version = m0.group(1), m0.group(2), m0.group(3), \
        int(m0.group(4))
    if version < 1:
        return None, [f"{vdir}: versions start at v0001"]
    if (base / vdir).exists():
        return None, [f"{vdir} already exists on the base branch; versions are immutable"]
    gdir = base / vdir.rsplit("/", 1)[0]
    existing = sorted(int(p.name[1:]) for p in gdir.iterdir()
                      if re.fullmatch(r"v[0-9]{4}", p.name)) if gdir.is_dir() else []
    expected = (max(existing) + 1) if existing else 1
    if version != expected:
        probs.append(f"{vdir}: the next version of this generator is v{expected:04d}")
    data, texts = {}, {}
    for r, m in items:
        name, f = m.group(5), r["filename"]
        p = fetched / "files" / f
        size = r.get("size")
        if not isinstance(size, int) or size > LIMITS[name]:
            probs.append(f"{f}: larger than {LIMITS[name]} bytes (or of unknown size)")
            continue
        if not p.is_file() or p.is_symlink():
            probs.append(f"{f}: its content could not be fetched")
            continue
        b = p.read_bytes()
        if len(b) != size or len(b) > LIMITS[name]:
            probs.append(f"{f}: its fetched size does not match")
            continue
        try:
            texts[name] = b.decode("utf-8")
        except UnicodeDecodeError:
            probs.append(f"{f}: not UTF-8")
            continue
        data[f] = b
    if probs:
        return None, probs
    try:
        man = json.loads(texts["manifest.json"])
    except json.JSONDecodeError as e:
        return None, [f"{vdir}/manifest.json: not JSON: {e}"]
    mp = schema.check(man, "generator") if isinstance(man, dict) else ["not a JSON object"]
    if mp:
        return None, [f"{vdir}/manifest.json: {p}" for p in mp]
    for k, v in (("role", role), ("family_id", family_id), ("generator_id", generator_id),
                 ("version", version)):
        if man[k] != v:
            probs.append(f"manifest.json: `{k}` is {man[k]!r}, but the path says {v!r}")
    want_parent = None if version == 1 else {"generator_id": generator_id, "version": version - 1}
    if man["parent"] != want_parent:
        probs.append(f"manifest.json: `parent` must be {json.dumps(want_parent)} (the previous "
                     "version of this generator)")
    fam = POL.family(pol, family_id)
    if fam is None:
        probs.append(f"manifest.json: family {family_id} is not approved in meta/learning.json "
                     "(a new family is a separate maintainer review)")
        return None, probs
    if fam["role"] != role:
        probs.append(f"manifest.json: family {family_id} is approved for {fam['role']}, not {role}")
    if man["family_revision"] != fam["revision"]:
        probs.append(f"manifest.json: family_revision is not the policy's pinned revision "
                     f"{fam['revision']}")
    if man["seed_bits"] != fam["seed_bits"]:
        probs.append(f"manifest.json: seed_bits {man['seed_bits']} differs from the family "
                     f"policy's {fam['seed_bits']}")
    if not 1 <= man["levels"] <= min(fam["max_levels"], POL.MAX_LEVELS):
        probs.append(f"manifest.json: levels must be 1..{fam['max_levels']}")
    ns = LI.generator_namespace(role, family_id, generator_id, version)
    for k in ("generate_decl", "certificate_decl"):
        if not man[k].startswith(ns + "."):
            probs.append(f"manifest.json: `{k}` must be declared in the namespace {ns}")
    boot = man.get("bootstrap")
    if boot is not None:
        if not fam["bootstrap"] or not POL.is_bootstrap_generator(pol, family_id, generator_id,
                                                                  version):
            probs.append("manifest.json: a bootstrap generator must be listed in the policy's "
                         "bootstrap_generators (a maintainer approval)")
        elif boot["approved_by"] != fam["approved_by"]:
            probs.append("manifest.json: bootstrap.approved_by is not the policy's approver")
    elif not man["source_refs"]:
        probs.append("manifest.json: source_refs must cite at least one verified DAG node "
                     "(or the generator must be a maintainer-approved bootstrap generator)")
    if man["source_refs"]:
        if records is None:
            probs.append("source_refs cannot be validated without the records branch")
        else:
            nodes = sources.corpus(base, records, pol["epoch"]["environment_id"], "0" * 40)
            probs += sources.ref_problems(man["source_refs"], nodes)
    gen_mod, cert_mod = ns + ".Generate", ns + ".Certificate"
    probs += [f"{vdir}/Generate.lean: {p}" for p in lean_problems(texts["Generate.lean"])]
    probs += [f"{vdir}/Certificate.lean: {p}"
              for p in lean_problems(texts["Certificate.lean"], (gen_mod,))]
    if probs:
        return None, probs
    info = {"role": role, "family_id": family_id, "generator_id": generator_id,
            "version": version, "dir": vdir,
            "files": {f: canon.sha256_bytes(b) for f, b in sorted(data.items())},
            "manifest": man, "generate_module": gen_mod, "certificate_module": cert_mod,
            "namespace": ns, "lean_family": fam["lean_family"], "lean_module": fam["lean_module"],
            "family_revision": fam["revision"], "seed_bits": fam["seed_bits"],
            "levels": man["levels"], "entropy_bits": fam["entropy_bits"],
            "max_descriptor_bits": fam["max_descriptor_bits"], "bootstrap": boot is not None,
            "source_refs": man["source_refs"], "generate_decl": man["generate_decl"],
            "certificate_decl": man["certificate_decl"]}
    return info, []


def notebook_route(base: Path, fetched: Path, rows: list[dict], pol: dict) \
        -> tuple[dict | None, list[str]]:
    if len(rows) != 1:
        return None, ["a notebook pull request changes exactly one notebook file"]
    r = rows[0]
    f = r.get("filename")
    role = NB.path_role(f)
    if role is None:
        return None, [f"{f}: not a notebook (notebooks/design.md or notebooks/cryptanalysis.md)"]
    if r.get("status") not in ("added", "modified") or r.get("previous_filename"):
        return None, [f"{f}: {r.get('status')}; a notebook pull request adds or modifies the "
                      "notebook (a rollback restores old bytes, it never deletes the file)"]
    if p := _regular(r):
        return None, [p]
    p = fetched / "files" / f
    if not p.is_file() or p.is_symlink():
        return None, [f"{f}: its content could not be fetched (or it is too large)"]
    data = p.read_bytes()
    if isinstance(r.get("size"), int) and r["size"] != len(data):
        return None, [f"{f}: its fetched size does not match"]
    probs = [f"{f}: {x}" for x in NB.problems(data, pol)]
    try:
        inc = NB.read_active_file(base, role)
    except ValueError as e:
        return None, [str(e)]
    if probs:
        return None, probs
    if inc == data:
        return None, [f"{f}: identical to the active notebook"]
    me, mi = NB.measure(data, pol), NB.measure(inc, pol)
    return {"role": role, "path": f, "status": r["status"], "sha256": me["sha256"],
            "bytes": me["bytes"], "tokens": me["tokens"], "tokenizer": me["tokenizer"],
            "incumbent_sha256": mi["sha256"], "incumbent_bytes": mi["bytes"],
            "incumbent_tokens": mi["tokens"]}, []
