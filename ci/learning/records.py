"""The append-only learning record store: a directory that is a checkout of the branch
`learning-records`, one JSONL file per kind (RECORDS.md, "Storage").

Every record is validated against its schema and its `record_id` recomputed before it is
appended. Appending is idempotent: a record whose `record_id` is already stored is skipped, so a
re-run of the same step (after a failed push, say) never duplicates a record. Nothing is ever
rewritten or deleted.
"""

from __future__ import annotations

import json
from pathlib import Path

from . import canon, schema

FILES = {
    "sigaba.learning.certification.v1": "certifications.jsonl",
    "sigaba.learning.calibration.v1": "calibrations.jsonl",
    "sigaba.learning.contract.v1": "contracts.jsonl",
    "sigaba.learning.trial.v1": "trials.jsonl",
    "sigaba.learning.comparison.v1": "comparisons.jsonl",
    "sigaba.learning.activation.v1": "activations.jsonl",
    "sigaba.learning.reveal.v1": "reveals.jsonl",
}
KIND_OF_FILE = {v: k for k, v in FILES.items()}
SHORT = {"certification": "sigaba.learning.certification.v1",
         "calibration": "sigaba.learning.calibration.v1",
         "contract": "sigaba.learning.contract.v1", "trial": "sigaba.learning.trial.v1",
         "comparison": "sigaba.learning.comparison.v1",
         "activation": "sigaba.learning.activation.v1", "reveal": "sigaba.learning.reveal.v1"}


class RecordError(Exception):
    pass


class Store:
    def __init__(self, root: Path | None):
        self.root = Path(root) if root is not None else None
        self._cache: dict[str, list[dict]] = {}

    def path(self, kind: str) -> Path:
        if self.root is None:
            raise RecordError("no record store")
        return self.root / FILES[kind]

    def read(self, kind: str) -> list[dict]:
        """The records of `kind` (full or short name), in order. Lines that do not validate are
        an error: the store is trusted output and a corrupt line must be looked at."""
        kind = SHORT.get(kind, kind)
        if kind in self._cache:
            return self._cache[kind]
        out: list[dict] = []
        if self.root is not None and (p := self.path(kind)).is_file():
            for i, line in enumerate(p.read_text().splitlines(), 1):
                if not line.strip():
                    continue
                try:
                    r = json.loads(line)
                except json.JSONDecodeError as e:
                    raise RecordError(f"{p.name}:{i}: not JSON: {e}") from None
                probs = schema.check_record(r) if isinstance(r, dict) else ["not an object"]
                if probs or r.get("schema") != kind:
                    raise RecordError(f"{p.name}:{i}: " + "; ".join(probs or ["wrong kind"]))
                out.append(r)
        self._cache[kind] = out
        return out

    def ids(self, kind: str) -> set[str]:
        return {r["record_id"] for r in self.read(kind)}

    def get(self, record_id: str) -> dict | None:
        for kind in FILES:
            for r in self.read(kind):
                if r["record_id"] == record_id:
                    return r
        return None

    def append(self, records: list[dict]) -> list[dict]:
        """Append the records not yet stored (all are validated first; nothing is written if one
        is invalid). Returns the ones written."""
        for r in records:
            probs = schema.check_record(r)
            if probs:
                raise RecordError(f"invalid {r.get('schema')} record: " + "; ".join(probs[:20]))
        written = []
        seen = {k: self.ids(k) for k in FILES}
        for r in records:
            kind = r["schema"]
            if r["record_id"] in seen[kind]:
                continue
            seen[kind].add(r["record_id"])
            written.append(r)
        if written:
            self.root.mkdir(parents=True, exist_ok=True)
            for r in written:
                with self.path(r["schema"]).open("a") as f:
                    f.write(canon.canonical(r).decode("utf-8") + "\n")
                self._cache.pop(r["schema"], None)
        return written

    def verify(self) -> list[str]:
        """Problems of the whole store (for `doctor`)."""
        probs = []
        for kind in FILES:
            try:
                rs = self.read(kind)
            except RecordError as e:
                probs.append(str(e))
                continue
            ids = [r["record_id"] for r in rs]
            if len(ids) != len(set(ids)):
                probs.append(f"{FILES[kind]}: duplicate record ids")
        return probs


def stamp(rec: dict, created_at: str, common: dict) -> dict:
    """A sealed record: `common` (core_revision, dag_snapshot, environment_id) and `created_at`
    added, then `record_id` (and a contract's `contract_id`)."""
    r = dict(rec)
    r.update(common)
    r["created_at"] = created_at
    return canon.seal(r)
