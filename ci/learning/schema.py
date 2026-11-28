"""A minimal JSON Schema validator (the subset `schemas/*.schema.json` use), standard library only.

Supported keywords: type, enum, const, pattern (full match), minLength, maxLength, minimum,
maximum, required, properties, additionalProperties, items, minItems, maxItems, uniqueItems,
maxProperties, anyOf, oneOf and `$ref` to `#/$defs/<name>` of the same document. Booleans are
never integers or numbers. Unknown keywords are an error of the schema, so that a typo cannot
silently weaken it.
"""

from __future__ import annotations

import json
import re
from functools import lru_cache
from pathlib import Path

from . import canon

SCHEMA_DIR = Path(__file__).resolve().parent / "schemas"

KNOWN = {"$schema", "$id", "title", "description", "$defs", "$ref", "type", "enum", "const",
         "pattern", "minLength", "maxLength", "minimum", "maximum", "required", "properties",
         "additionalProperties", "items", "minItems", "maxItems", "uniqueItems", "anyOf", "oneOf",
         "maxProperties"}
TYPES = {"object": dict, "array": list, "string": str, "integer": int, "boolean": bool,
         "number": (int, float), "null": type(None)}

# The record kinds and their schema files.
KINDS = {
    "sigaba.generator.v1": "generator",
    "sigaba.learning.policy.v1": "policy",
    "sigaba.learning.certification.v1": "certification",
    "sigaba.learning.calibration.v1": "calibration",
    "sigaba.learning.contract.v1": "contract",
    "sigaba.learning.trial.v1": "trial",
    "sigaba.learning.comparison.v1": "comparison",
    "sigaba.learning.activation.v1": "activation",
    "sigaba.learning.reveal.v1": "reveal",
    "sigaba.learning.route.v1": "route",
    "sigaba.learning.certify-result.v1": "certify-result",
}


@lru_cache(maxsize=None)
def load(name: str) -> dict:
    return json.loads((SCHEMA_DIR / f"{name}.schema.json").read_text())


def validate(obj, schema: dict, where: str = "$", root: dict | None = None) -> list[str]:
    """The problems of `obj` against `schema` (an empty list when it conforms)."""
    root = schema if root is None else root
    unknown = set(schema) - KNOWN
    if unknown:
        raise ValueError(f"schema at {where}: unsupported keywords {sorted(unknown)}")
    if "$ref" in schema:
        ref = schema["$ref"]
        if not ref.startswith("#/$defs/"):
            raise ValueError(f"schema at {where}: unsupported $ref {ref}")
        return validate(obj, root["$defs"][ref[len("#/$defs/"):]], where, root)
    errs: list[str] = []
    t = schema.get("type")
    if t is not None:
        allowed = t if isinstance(t, list) else [t]
        if not any(isinstance(obj, TYPES[x]) and not (x in ("integer", "number") and
                                                      isinstance(obj, bool)) for x in allowed):
            return [f"{where}: expected {'/'.join(allowed)}"]
    if "enum" in schema and not any(_same(obj, e) for e in schema["enum"]):
        errs.append(f"{where}: must be one of {schema['enum']}")
    if "const" in schema and not _same(obj, schema["const"]):
        errs.append(f"{where}: must be {schema['const']!r}")
    if isinstance(obj, str):
        if "pattern" in schema and not re.fullmatch(schema["pattern"], obj):
            errs.append(f"{where}: does not match {schema['pattern']}")
        if "maxLength" in schema and len(obj) > schema["maxLength"]:
            errs.append(f"{where}: longer than {schema['maxLength']}")
        if "minLength" in schema and len(obj) < schema["minLength"]:
            errs.append(f"{where}: shorter than {schema['minLength']}")
    if isinstance(obj, (int, float)) and not isinstance(obj, bool):
        if "minimum" in schema and obj < schema["minimum"]:
            errs.append(f"{where}: less than {schema['minimum']}")
        if "maximum" in schema and obj > schema["maximum"]:
            errs.append(f"{where}: greater than {schema['maximum']}")
    if isinstance(obj, dict):
        for k in schema.get("required", []):
            if k not in obj:
                errs.append(f"{where}: missing `{k}`")
        if "maxProperties" in schema and len(obj) > schema["maxProperties"]:
            errs.append(f"{where}: more than {schema['maxProperties']} keys")
        props = schema.get("properties", {})
        extra = schema.get("additionalProperties", True)
        for k, v in obj.items():
            if k in props:
                errs += validate(v, props[k], f"{where}.{k}", root)
            elif extra is False:
                errs.append(f"{where}: unknown key `{k}`")
            elif isinstance(extra, dict):
                errs += validate(v, extra, f"{where}.{k}", root)
    if isinstance(obj, list):
        if "minItems" in schema and len(obj) < schema["minItems"]:
            errs.append(f"{where}: fewer than {schema['minItems']} items")
        if "maxItems" in schema and len(obj) > schema["maxItems"]:
            errs.append(f"{where}: more than {schema['maxItems']} items")
        if schema.get("uniqueItems"):
            seen = [canon.canonical(v) for v in obj]
            if len(set(seen)) != len(seen):
                errs.append(f"{where}: items are not unique")
        if "items" in schema:
            for i, v in enumerate(obj):
                errs += validate(v, schema["items"], f"{where}[{i}]", root)
    if "anyOf" in schema:
        if not any(not validate(obj, s, where, root) for s in schema["anyOf"]):
            errs.append(f"{where}: matches none of the allowed forms")
    if "oneOf" in schema:
        n = sum(1 for s in schema["oneOf"] if not validate(obj, s, where, root))
        if n != 1:
            errs.append(f"{where}: matches {n} of the forms, not exactly one")
    return errs


def _same(a, b) -> bool:
    if isinstance(a, bool) != isinstance(b, bool):
        return False
    return a == b


def check(obj, name: str | None = None) -> list[str]:
    """The problems of `obj` against the schema `name` (or, by default, the one its `schema`
    field names)."""
    if name is None:
        kind = obj.get("schema") if isinstance(obj, dict) else None
        if kind not in KINDS:
            return [f"$.schema: unknown record kind {kind!r}"]
        name = KINDS[kind]
    return validate(obj, load(name))


def check_record(rec: dict) -> list[str]:
    """Schema problems, and a `record_id` (and a contract's `contract_id`) that does not match
    the record's content."""
    probs = check(rec)
    if probs:
        return probs
    rid = canon.record_id(rec)
    if "record_id" in rec and rec["record_id"] != rid:
        probs.append(f"$.record_id: {rec['record_id']} is not the record's digest {rid}")
    if rec.get("schema") == "sigaba.learning.contract.v1" and rec.get("contract_id") != rid:
        probs.append("$.contract_id: must equal the record's digest")
    return probs
