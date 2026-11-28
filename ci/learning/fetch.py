"""Fetch a pull request's changed files as data, through the GitHub API (no checkout of it).

Modelled on the core's `dag_tools.py fetch`, which downloads only DAG nodes. This one lists every
changed file and downloads the contents of the added or modified files under `generators/` and
`notebooks/` only:

    OUT/files.json   {"revision": HEAD, "files": [{filename, status, type, mode, size,
                                                   [previous_filename]}]}
    OUT/files/<path> the downloaded contents

`type` and `mode` come from the tree entry of `head` itself (`blob` with `100644`/`100755` is a
regular file; `120000` a symbolic link, `commit` a submodule: reported, never downloaded). The
event's commits do not move, so everything is about `head`. The token is `$GITHUB_TOKEN` (read
only); it is never printed. Nothing here interprets the contents. The base version of a modified
notebook is read by `route` from the base checkout, not fetched.
"""

from __future__ import annotations

import base64
import json
import os
import re
import urllib.request
from pathlib import Path
from typing import Callable

COMPARE_FILES = 300          # the compare API lists at most this many files
MAX_FILE_BYTES = 1024 * 1024
MAX_DOWNLOADS = 8            # a learning pull request has at most 3 files; more are not fetched
LEARNING_PREFIXES = ("generators/", "notebooks/")

Api = Callable[[str], object]


def github_api(token: str | None) -> Api:
    def api(path: str):
        req = urllib.request.Request("https://api.github.com" + path)
        req.add_header("Accept", "application/vnd.github+json")
        req.add_header("User-Agent", "sigaba-learning-fetch")
        if token:
            req.add_header("Authorization", f"Bearer {token}")
        with urllib.request.urlopen(req, timeout=60) as r:
            return json.loads(r.read())
    return api


def tree_diff(api: Api, repo: str, old: str, new: str) -> list[dict]:
    """The changed files between two commits from their full trees (for large comparisons)."""
    def flat(sha: str) -> dict[str, dict]:
        t = api(f"/repos/{repo}/git/trees/{sha}?recursive=1")
        if t.get("truncated"):
            raise SystemExit("the tree is too large to list")
        return {e["path"]: e for e in t.get("tree", []) if e.get("type") != "tree"}
    a, b = flat(old), flat(new)
    rows = []
    for p in sorted(set(a) | set(b)):
        if p not in a:
            rows.append({"filename": p, "status": "added"})
        elif p not in b:
            rows.append({"filename": p, "status": "removed"})
        elif a[p].get("sha") != b[p].get("sha") or a[p].get("mode") != b[p].get("mode"):
            rows.append({"filename": p, "status": "modified"})
    return rows


def wanted(row: dict) -> bool:
    return row["status"] in ("added", "modified") and \
        row["filename"].startswith(LEARNING_PREFIXES)


def fetch(repo: str, out: Path, base: str, head: str, api: Api) -> list[dict]:
    if not re.fullmatch(r"[\w.-]+/[\w.-]+", repo or ""):
        raise SystemExit(f"not a repository: {repo!r}")
    for sha in (base, head):
        if not re.fullmatch(r"[0-9a-f]{40}", sha or ""):
            raise SystemExit(f"not a commit: {sha!r}")
    cmp = api(f"/repos/{repo}/compare/{base}...{head}")
    files = cmp.get("files", [])
    if len(files) >= COMPARE_FILES:
        merge_base = (cmp.get("merge_base_commit") or {}).get("sha", "")
        if not re.fullmatch(r"[0-9a-f]{40}", merge_base):
            raise SystemExit("too many changed files, and no merge base to list them from")
        files = tree_diff(api, repo, merge_base, head)
    trees: dict[str, dict] = {}

    def tree(sha: str) -> dict:
        if sha not in trees:
            t = api(f"/repos/{repo}/git/trees/{sha}")
            trees[sha] = {e["path"]: e for e in t.get("tree", [])}
        return trees[sha]

    root = api(f"/repos/{repo}/git/commits/{head}")["tree"]["sha"]

    def entry(path: str) -> dict | None:
        node = {"type": "tree", "sha": root}
        for part in path.split("/"):
            if node.get("type") != "tree":
                return None
            node = tree(node["sha"]).get(part)
            if node is None:
                return None
        return node

    out.mkdir(parents=True, exist_ok=True)
    downloads = sum(1 for f in files if wanted(f))
    rows = []
    for f in files:
        row = {"filename": f["filename"], "status": f["status"], "type": None, "mode": None,
               "size": None}
        if f.get("previous_filename"):
            row["previous_filename"] = f["previous_filename"]
        if f["status"] != "removed":
            e = entry(f["filename"])
            if e is not None:
                row.update(type=e.get("type"), mode=e.get("mode"), size=e.get("size"))
                if wanted(f) and downloads <= MAX_DOWNLOADS and e.get("type") == "blob" and \
                        e.get("mode") in ("100644", "100755") and \
                        (e.get("size") or 0) <= MAX_FILE_BYTES and _safe(f["filename"]):
                    blob = api(f"/repos/{repo}/git/blobs/{e['sha']}")
                    data = base64.b64decode(blob["content"]) \
                        if blob.get("encoding") == "base64" else blob["content"].encode()
                    row["size"] = len(data)
                    if len(data) <= MAX_FILE_BYTES:
                        dst = out / "files" / f["filename"]
                        dst.parent.mkdir(parents=True, exist_ok=True)
                        dst.write_bytes(data)
        rows.append(row)
    (out / "files.json").write_text(json.dumps({"revision": head, "files": rows}, indent=1) + "\n")
    return rows


def _safe(path: str) -> bool:
    parts = path.split("/")
    return all(p not in ("", ".", "..") for p in parts) and "\\" not in path and \
        not path.startswith("/")


def main(repo: str, base: str, head: str, out: Path) -> list[dict]:
    return fetch(repo, Path(out), base, head, github_api(os.environ.get("GITHUB_TOKEN")))


def fetch_local(repo_dir: Path, base: str, head: str, out: Path) -> list[dict]:
    """The same output as `fetch`, read from a local checkout that has both commits (the
    post-merge job: what a merge added to `main`). Contents are read from `head`'s tree; symbolic
    links and submodules are reported with their mode and not downloaded."""
    import subprocess

    def git(*args: str) -> bytes:
        return subprocess.run(["git", "-C", str(repo_dir), *args], check=True,
                              capture_output=True).stdout

    for sha in (base, head):
        if not re.fullmatch(r"[0-9a-f]{40}", sha or ""):
            raise SystemExit(f"not a commit: {sha!r}")
    status = {"A": "added", "M": "modified", "D": "removed", "T": "modified"}
    files = []
    parts = [p.decode() for p in git("diff", "--name-status", "--no-renames", "-z", base,
                                      head).split(b"\0") if p]
    for i in range(0, len(parts) - 1, 2):
        files.append({"filename": parts[i + 1], "status": status.get(parts[i][:1], "modified")})
    out.mkdir(parents=True, exist_ok=True)
    downloads = sum(1 for f in files if wanted(f))
    rows = []
    for f in files:
        row = {"filename": f["filename"], "status": f["status"], "type": None, "mode": None,
               "size": None}
        if f["status"] != "removed":
            ls = git("ls-tree", "-l", head, "--", f["filename"]).decode().split("\t")[0].split()
            if len(ls) >= 4:
                mode, typ, _sha, size = ls[:4]
                row.update(type=typ, mode=mode, size=int(size) if size.isdigit() else None)
                if wanted(f) and downloads <= MAX_DOWNLOADS and typ == "blob" and \
                        mode in ("100644", "100755") and (row["size"] or 0) <= MAX_FILE_BYTES \
                        and _safe(f["filename"]):
                    data = git("show", f"{head}:{f['filename']}")
                    dst = out / "files" / f["filename"]
                    dst.parent.mkdir(parents=True, exist_ok=True)
                    dst.write_bytes(data)
        rows.append(row)
    (out / "files.json").write_text(json.dumps({"revision": head, "files": rows}, indent=1) + "\n")
    return rows
