"""Role notebooks: exact bytes, SHA-256, size and the (proxy) token count.

A notebook is `notebooks/<role>.md` on `main`, UTF-8 Markdown, data and never instructions. Its
identity is the SHA-256 of its exact bytes: nothing here rewrites it. A missing file is the empty
notebook (`EMPTY_SHA256`).

Tokens: no tokenizer of the evaluation model is pinned, so the count is the documented proxy
`proxy-bytes-div-3` version 1, `ceil(bytes / 3)`. It is reported as a proxy, never as an exact
count (`exact: false`). For English Markdown, BPE tokenizers average about four bytes per token,
so the proxy over-counts, which keeps the cap conservative.
"""

from __future__ import annotations

from pathlib import Path

from . import canon

ROLES = ("design", "cryptanalysis")
PATHS = {r: f"notebooks/{r}.md" for r in ROLES}
EMPTY_SHA256 = canon.sha256_bytes(b"")
PROXY = {"kind": "proxy-bytes-div-3", "version": "1"}


def path_role(path: str) -> str | None:
    return next((r for r, p in PATHS.items() if p == path), None)


def tokens(data: bytes, tokenizer: dict) -> int:
    if tokenizer == PROXY:
        return (len(data) + 2) // 3
    raise ValueError(f"no implementation of the tokenizer {tokenizer}; a pinned tokenizer must "
                     "be added to ci/learning/notebooks.py before the policy can name it")


def measure(data: bytes, policy: dict) -> dict:
    tok = policy["notebooks"]["tokenizer"]
    return {"sha256": canon.sha256_bytes(data), "bytes": len(data), "tokens": tokens(data, tok),
            "tokenizer": dict(tok), "exact_tokens": False}


def problems(data: bytes, policy: dict) -> list[str]:
    """Why `data` cannot be a notebook under `policy`."""
    probs = []
    caps = policy["notebooks"]
    try:
        text = data.decode("utf-8")
    except UnicodeDecodeError as e:
        return [f"not UTF-8 ({e.reason} at byte {e.start})"]
    if data.startswith(b"\xef\xbb\xbf"):
        probs.append("starts with a byte order mark; save it as UTF-8 without BOM")
    if "\r" in text:
        probs.append("contains carriage returns; use LF line endings (the notebook is hashed "
                     "byte for byte and never rewritten)")
    if "\x00" in text:
        probs.append("contains NUL characters")
    if len(data) > caps["max_bytes"]:
        probs.append(f"{len(data)} bytes, above the cap of {caps['max_bytes']}")
    n = tokens(data, caps["tokenizer"])
    if n > caps["max_tokens"]:
        probs.append(f"{n} tokens ({caps['tokenizer']['kind']} proxy), above the cap of "
                     f"{caps['max_tokens']}")
    return probs


def read_active_file(base: Path, role: str) -> bytes:
    """The notebook bytes of `role` in a checkout (empty when the file does not exist)."""
    p = Path(base) / PATHS[role]
    if p.is_symlink():
        raise ValueError(f"{PATHS[role]} is a symbolic link")
    return p.read_bytes() if p.is_file() else b""
