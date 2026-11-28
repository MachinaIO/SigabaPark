"""Canonical JSON, digests and record identities (RECORDS.md, "Conventions").

Canonical JSON is UTF-8 with sorted object keys, separators `,` and `:`, no NaN or Infinity, and
floats written with Python's `repr` (the shortest round-tripping form of a finite float).
"""

from __future__ import annotations

import hashlib
import json
import math
import re
import time

SHA256 = re.compile(r"sha256:[0-9a-f]{64}")
GIT_SHA = re.compile(r"[0-9a-f]{40}")
# Fields that never enter a record's identity.
VOLATILE = ("record_id", "created_at", "generated_at")


def _check(obj, where: str = "$") -> None:
    if isinstance(obj, float) and not math.isfinite(obj):
        raise ValueError(f"{where}: NaN or Infinity is not canonical JSON")
    if isinstance(obj, dict):
        for k, v in obj.items():
            if not isinstance(k, str):
                raise ValueError(f"{where}: object keys must be strings")
            _check(v, f"{where}.{k}")
    elif isinstance(obj, (list, tuple)):
        for i, v in enumerate(obj):
            _check(v, f"{where}[{i}]")
    elif not (obj is None or isinstance(obj, (str, int, float, bool))):
        raise ValueError(f"{where}: {type(obj).__name__} is not JSON")


def canonical(obj) -> bytes:
    """The canonical JSON bytes of `obj`."""
    _check(obj)
    return json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=False,
                      allow_nan=False).encode("utf-8")


def sha256_bytes(data: bytes) -> str:
    return "sha256:" + hashlib.sha256(data).hexdigest()


def digest(obj) -> str:
    """`sha256:` of the canonical JSON of `obj`."""
    return sha256_bytes(canonical(obj))


def identity_fields(rec: dict) -> dict:
    """The part of a record its identity covers: everything but `record_id`, `created_at` and
    `generated_at`, and for a contract also `contract_id` (which *is* its record id)."""
    drop = set(VOLATILE)
    if rec.get("schema") == "sigaba.learning.contract.v1":
        drop.add("contract_id")
    return {k: v for k, v in rec.items() if k not in drop}


def record_id(rec: dict) -> str:
    return digest(identity_fields(rec))


def seal(rec: dict) -> dict:
    """`rec` with its `record_id` (and a contract's `contract_id`) filled in."""
    out = dict(rec)
    rid = record_id(out)
    out["record_id"] = rid
    if out.get("schema") == "sigaba.learning.contract.v1":
        out["contract_id"] = rid
    return out


def now(clock=time.time) -> str:
    return time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime(clock()))


def parse_time(s: str) -> float:
    """Seconds since the epoch of an ISO 8601 UTC timestamp `YYYY-MM-DDTHH:MM:SSZ` (or a date)."""
    import calendar
    if re.fullmatch(r"\d{4}-\d{2}-\d{2}", s):
        s += "T00:00:00Z"
    return float(calendar.timegm(time.strptime(s, "%Y-%m-%dT%H:%M:%SZ")))
