"""Progress report generator for certified curriculum and notebook learning.

Reads the append-only learning records (JSONL files, see ``ci/learning/RECORDS.md``) and writes a
static, self-contained report (core specification, section 11):

- ``index.html``: inline SVG charts, CSS and a small filter script (no network, no CDN), with a data
  table under every chart and a static fallback when JavaScript is disabled;
- ``LEARNING.md``: a short summary per role;
- ``data.json``: the derived data, every point carrying the ``record_ids`` it was derived from;
- ``generators.csv``, ``calibrations.csv``, ``comparisons.csv``, ``activations.csv``,
  ``anchors.csv``.

The report is a pure function of the records (and optional policy) except for a generated-at
timestamp, which ``--as-of`` omits (``--as-of`` also drops records created after that date).
Generating a report makes no model, provider or network call. All record text is untrusted: it is
escaped for HTML, Markdown and CSV, and notebook text is never read or rendered.

Usage::

    python3 -m ci.learning.report --records DIR --out DIR [--as-of YYYY-MM-DD]
                                  [--policy meta/learning.json]
"""

import argparse
import csv
import datetime
import hashlib
import html
import io
import json
import math
import os
import re
import sys
from fractions import Fraction

REPORT_SCHEMA = "sigaba.learning.report.v1"
ROLES = ("design", "cryptanalysis")
ROLE_TITLES = {"design": "Design", "cryptanalysis": "Cryptanalysis"}
KINDS = (
    ("certifications", "sigaba.learning.certification.v1"),
    ("calibrations", "sigaba.learning.calibration.v1"),
    ("contracts", "sigaba.learning.contract.v1"),
    ("trials", "sigaba.learning.trial.v1"),
    ("comparisons", "sigaba.learning.comparison.v1"),
    ("activations", "sigaba.learning.activation.v1"),
    ("reveals", "sigaba.learning.reveal.v1"),
)
ROLE_KINDS = ("certifications", "calibrations", "contracts", "trials", "comparisons", "activations")
PASS_VERDICTS = ("pass_performance", "pass_compression")
VERDICTS = ("pass_performance", "pass_compression", "fail", "inconclusive", "awaiting_evaluator",
            "stale", "infra_error")
STAGE_GROUPS = {"calibration": "exploration", "screen": "promotion", "confirm": "promotion",
                "anchor": "anchor", "transfer": "transfer"}
STAGE_GROUP_ORDER = ("exploration", "promotion", "anchor", "transfer", "unknown")
SPEC_CURRICULUM_DEFAULTS = {"target": "0.40", "lo": "0.20", "hi": "0.60"}
ADVERSARY_STATEMENT = (
    "The adversary model of every record is classical. Nothing in this report certifies "
    "post-quantum security.")
DIFFICULTY_CAPTION = "difficulty = 1 \u2212 p for the stated reference profile"


# ---------------------------------------------------------------------------------------------
# Small value helpers
# ---------------------------------------------------------------------------------------------

def canonical_json(obj):
    return json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=False,
                      allow_nan=False).encode("utf-8")


def sha256_of(obj):
    return "sha256:" + hashlib.sha256(canonical_json(obj)).hexdigest()


def short(value, n=12):
    """Shortened identifier for display (full value is always kept in data and tooltips)."""
    s = "" if value is None else str(value)
    if s.startswith("sha256:") and len(s) > 7 + n:
        return s[7:7 + n]
    if len(s) > n + 8:
        return s[:n + 6] + "\u2026"
    return s


def as_int(v):
    if isinstance(v, bool) or not isinstance(v, int):
        return None
    return v


def as_num(v):
    if isinstance(v, bool) or not isinstance(v, (int, float)):
        return None
    if isinstance(v, float) and not math.isfinite(v):
        return None
    return v


def as_str(v):
    return v if isinstance(v, str) else (None if v is None else str(v))


def parse_ts(value):
    """Parse an ISO 8601 UTC timestamp; returns an aware datetime or None."""
    if not isinstance(value, str) or not value:
        return None
    text = value.strip()
    if text.endswith("Z"):
        text = text[:-1] + "+00:00"
    try:
        dt = datetime.datetime.fromisoformat(text)
    except ValueError:
        return None
    if dt.tzinfo is None:
        return None
    return dt.astimezone(datetime.timezone.utc)


_EPOCH = datetime.datetime(1970, 1, 1, tzinfo=datetime.timezone.utc)


def day_number(dt):
    return (dt - _EPOCH).total_seconds() / 86400.0


def date_of(rec):
    return rec["_ts"].strftime("%Y-%m-%d")


def wilson(successes, n, z=1.959963984540054):
    """Wilson 95% score interval (an estimate under the independent sampling model)."""
    if n is None or successes is None or n <= 0 or successes < 0 or successes > n:
        return None
    p = successes / n
    denom = 1 + z * z / n
    centre = p + z * z / (2 * n)
    radius = z * math.sqrt(p * (1 - p) / n + z * z / (4 * n * n))
    return (max(0.0, (centre - radius) / denom), min(1.0, (centre + radius) / denom))


def frac_of(v):
    """Rational value from a policy/contract number or [num, den] pair (via str, no float error)."""
    try:
        if isinstance(v, list) and len(v) == 2 and all(as_int(x) is not None for x in v) \
                and v[1] != 0:
            return Fraction(v[0], v[1])
        if isinstance(v, bool):
            return None
        if isinstance(v, (int, float, str)):
            return Fraction(str(v))
    except (ValueError, ZeroDivisionError):
        return None
    return None


def frac_str(f):
    if f is None:
        return None
    return str(f.numerator) if f.denominator == 1 else "%d/%d" % (f.numerator, f.denominator)


def pct(v, digits=1):
    return "n/a" if v is None else ("%." + str(digits) + "f%%") % (100.0 * v)


def pp(v, digits=1):
    return "n/a" if v is None else ("%+." + str(digits) + "f pp") % v


def ratio(num, den):
    if num is None or den is None or den <= 0:
        return None
    return num / den


def rid(rec):
    return rec.get("record_id")


def rids(*recs):
    out = []
    for r in recs:
        if r is not None and rid(r) and rid(r) not in out:
            out.append(rid(r))
    return out


# ---------------------------------------------------------------------------------------------
# Loading
# ---------------------------------------------------------------------------------------------

def _reject_constant(name):
    raise ValueError("non-finite number %s" % name)


def _record_id_ok(kind, obj):
    body = {k: v for k, v in obj.items()
            if k not in ("record_id", "created_at", "generated_at")}
    if kind == "contracts":
        body.pop("contract_id", None)
    try:
        return sha256_of(body) == obj.get("record_id")
    except (TypeError, ValueError):
        return False


def load_records(records_dir, as_of=None):
    """Load every JSONL record file. Missing files are an empty state; malformed lines are skipped
    and reported. With ``as_of`` (a date), records created after the end of that day are dropped.
    """
    records = {kind: [] for kind, _ in KINDS}
    issues = []
    inputs = {}
    seen = set()
    cutoff = None
    if as_of is not None:
        cutoff = datetime.datetime.combine(as_of, datetime.time(23, 59, 59, 999999),
                                           tzinfo=datetime.timezone.utc)
    for kind, schema in KINDS:
        fname = kind + ".jsonl"
        path = os.path.join(records_dir, fname)
        info = {"present": False, "lines": 0, "loaded": 0, "skipped": 0, "after_as_of": 0}
        inputs[fname] = info
        if not os.path.isfile(path):
            continue
        info["present"] = True
        with open(path, "rb") as fh:
            data = fh.read()
        for lineno, raw in enumerate(data.split(b"\n"), 1):
            if not raw.strip():
                continue
            info["lines"] += 1

            def bad(problem, record_id=None):
                info["skipped"] += 1
                issues.append({"file": fname, "line": lineno, "record_id": record_id,
                               "problem": problem, "action": "skipped"})

            try:
                obj = json.loads(raw.decode("utf-8"), parse_constant=_reject_constant)
            except (UnicodeDecodeError, ValueError) as exc:
                bad("invalid JSON: %s" % str(exc)[:120])
                continue
            if not isinstance(obj, dict):
                bad("not a JSON object")
                continue
            record_id = obj.get("record_id")
            if not isinstance(record_id, str) or not record_id:
                bad("missing record_id")
                continue
            if obj.get("schema") != schema:
                bad("schema is %r, expected %r" % (obj.get("schema"), schema), record_id)
                continue
            ts = parse_ts(obj.get("created_at"))
            if ts is None:
                bad("missing or invalid created_at", record_id)
                continue
            if kind in ROLE_KINDS and obj.get("role") not in ROLES:
                bad("missing or unknown role", record_id)
                continue
            if record_id in seen:
                bad("duplicate record_id", record_id)
                continue
            if cutoff is not None and ts > cutoff:
                info["after_as_of"] += 1
                continue
            seen.add(record_id)
            if not _record_id_ok(kind, obj):
                issues.append({"file": fname, "line": lineno, "record_id": record_id,
                               "problem": "record_id does not match the canonical content hash",
                               "action": "kept"})
            obj["_ts"] = ts
            obj["_kind"] = kind
            records[kind].append(obj)
            info["loaded"] += 1
        records[kind].sort(key=lambda r: (r["_ts"], r["record_id"]))
    return records, issues, inputs


def load_policy(policy):
    if policy is None:
        return None
    if isinstance(policy, dict):
        return policy
    with open(policy, "r", encoding="utf-8") as fh:
        obj = json.load(fh, parse_constant=_reject_constant)
    if not isinstance(obj, dict):
        raise ValueError("policy is not a JSON object")
    return obj


def policy_view(policy):
    """The policy values the report uses, with their source."""
    view = {"source": "none", "policy_id": None, "epoch_id": None,
            "curriculum": dict(SPEC_CURRICULUM_DEFAULTS),
            "curriculum_source": "specification defaults (no policy supplied)",
            "max_tokens": None, "max_bytes": None, "tokenizer": None, "families": {}}
    if not policy:
        return view
    view["source"] = "policy"
    view["policy_id"] = as_str(policy.get("policy_id"))
    epoch = policy.get("epoch") if isinstance(policy.get("epoch"), dict) else {}
    view["epoch_id"] = as_str(epoch.get("id"))
    cur = policy.get("curriculum") if isinstance(policy.get("curriculum"), dict) else {}
    found = False
    for key in ("target", "lo", "hi"):
        f = frac_of(cur.get(key))
        if f is not None:
            view["curriculum"][key] = str(cur.get(key))
            found = True
    if found:
        view["curriculum_source"] = "policy %s" % (view["policy_id"] or "(no policy_id)")
    nb = policy.get("notebooks") if isinstance(policy.get("notebooks"), dict) else {}
    view["max_tokens"] = as_int(nb.get("max_tokens"))
    view["max_bytes"] = as_int(nb.get("max_bytes"))
    tok = nb.get("tokenizer")
    if isinstance(tok, dict):
        view["tokenizer"] = "%s v%s" % (tok.get("kind"), tok.get("version"))
    fams = policy.get("families")
    if isinstance(fams, list):
        for fam in fams:
            if isinstance(fam, dict) and isinstance(fam.get("family_id"), str):
                view["families"][fam["family_id"]] = {
                    "role": as_str(fam.get("role")),
                    "entropy_bits": as_int(fam.get("entropy_bits")),
                    "group": as_str(fam.get("group")),
                    "assessment": as_str(fam.get("assessment"))}
    return view


# ---------------------------------------------------------------------------------------------
# Derivations (one function per chart); every point carries ``record_ids``
# ---------------------------------------------------------------------------------------------

def vkey(rec):
    return (as_str(rec.get("family_id")), as_str(rec.get("generator_id")),
            as_int(rec.get("version")))


def vlabel(key):
    return "%s/%s v%s" % (key[0], key[1], key[2])


def derive_library(certs, calibrations):
    latest = {}
    first_certified = {}
    generators, families = set(), set()
    points = []
    for rec in certs:
        key = vkey(rec)
        status = as_str(rec.get("status"))
        latest[key] = rec
        if status == "certified" and key not in first_certified:
            first_certified[key] = rec
            generators.add(key[:2])
            families.add(key[0])
        counts = {s: 0 for s in ("certified", "quarantined", "superseded", "rejected", "other")}
        for k, r in latest.items():
            s = as_str(r.get("status"))
            counts[s if s in counts else "other"] += 1
        points.append({
            "date": date_of(rec), "created_at": rec.get("created_at"), "event": status,
            "family_id": key[0], "generator_id": key[1], "version": key[2],
            "unique_generators": len(generators), "certified_versions": len(first_certified),
            "families": len(families), "current_status_counts": counts,
            "record_ids": rids(rec)})
    # Final state.
    current = {}
    for key, r in latest.items():
        current.setdefault(as_str(r.get("status")) or "other", []).append(key)
    cal_latest = {}
    for cal in calibrations:
        cal_latest[(vkey(cal), as_int(cal.get("level")), as_str(cal.get("profile_id")))] = cal
    eligible = {}
    for (key, _level, _profile), cal in cal_latest.items():
        if cal.get("eligibility") == "eligible" and key in latest \
                and latest[key].get("status") == "certified":
            eligible.setdefault(key, []).append(rid(cal))
    cert_now = sorted(k for k, r in latest.items() if r.get("status") == "certified")
    sources = set()
    for key, rec in first_certified.items():
        refs = rec.get("source_refs")
        if isinstance(refs, list):
            for ref in refs:
                if isinstance(ref, dict) and isinstance(ref.get("node_id"), str):
                    sources.add(ref["node_id"])
    summary = {
        "ever_certified_versions": len(first_certified),
        "ever_certified_generators": len(generators),
        "ever_certified_families": len(families),
        "current_certified_versions": len(cert_now),
        "current_certified_generators": len({k[:2] for k in cert_now}),
        "current_certified_families": len({k[0] for k in cert_now}),
        "current_quarantined_versions": sum(1 for r in latest.values()
                                            if r.get("status") == "quarantined"),
        "current_superseded_versions": sum(1 for r in latest.values()
                                           if r.get("status") == "superseded"),
        "rejected_versions": sum(1 for r in latest.values() if r.get("status") == "rejected"),
        "eligible_versions": len(eligible),
        "verified_source_nodes": len(sources),
        "record_ids": sorted(rid(r) for r in latest.values()),
    }
    rows = []
    for key in sorted(latest, key=lambda k: tuple("" if x is None else str(x) for x in k)):
        r = latest[key]
        all_ids = [rid(c) for c in certs if vkey(c) == key]
        first = first_certified.get(key)
        rows.append({
            "family_id": key[0], "generator_id": key[1], "version": key[2],
            "status": as_str(r.get("status")), "reason": as_str(r.get("reason")),
            "seed_bits": as_int(r.get("seed_bits")), "entropy_bits": as_int(r.get("entropy_bits")),
            "required_bits": as_int(r.get("required_bits")), "levels": as_int(r.get("levels")),
            "equivalence": as_str(r.get("equivalence")), "bootstrap": r.get("bootstrap"),
            "first_certified_at": first.get("created_at") if first else None,
            "latest_at": r.get("created_at"), "pr": r.get("pr"), "head": as_str(r.get("head")),
            "author": as_str(r.get("author")), "eligible": key in eligible,
            "record_ids": all_ids + eligible.get(key, [])})
    return {"points": points, "summary": summary, "rows": rows}


def derive_diversity(certs, pview):
    by_family = {}
    for rec in certs:
        if rec.get("status") != "certified":
            continue
        fam = as_str(rec.get("family_id"))
        by_family.setdefault(fam, []).append(rec)
    panels = []
    for fam in sorted(by_family, key=lambda f: "" if f is None else f):
        segments = []
        current_key = None
        for rec in by_family[fam]:
            seg_key = (as_str(rec.get("equivalence")), as_str(rec.get("family_revision")))
            k = as_int(rec.get("seed_bits"))
            h = as_int(rec.get("entropy_bits"))
            req = as_int(rec.get("required_bits"))
            req_source = "certification record"
            if req is None and fam in pview["families"]:
                req = pview["families"][fam]["entropy_bits"]
                req_source = "policy"
            point = {
                "date": date_of(rec), "created_at": rec.get("created_at"),
                "generator_id": as_str(rec.get("generator_id")),
                "version": as_int(rec.get("version")), "seed_bits": k,
                "certified_lower_bound_bits": h, "required_bits": req,
                "required_source": req_source,
                "h_over_k": (h / k) if (h is not None and k) else None,
                "equivalence": seg_key[0], "family_revision": seg_key[1],
                "record_ids": rids(rec)}
            if seg_key != current_key:
                segments.append({"equivalence": seg_key[0], "family_revision": seg_key[1],
                                 "points": []})
                current_key = seg_key
            segments[-1]["points"].append(point)
        panels.append({"family_id": fam, "segments": segments})
    return {"panels": panels}


def derive_difficulty(calibrations, pview):
    panels = {}
    for cal in calibrations:
        key = vkey(cal)
        pkey = (as_str(cal.get("profile_id")), as_str(cal.get("reference_notebook_sha256")),
                key)
        n = as_int(cal.get("n"))
        s = as_int(cal.get("successes"))
        p_hat = as_num(cal.get("p_hat"))
        ci = cal.get("ci") if isinstance(cal.get("ci"), dict) else None
        available = bool(n) and n > 0 and p_hat is not None
        notes = []
        if available and s is not None and abs(p_hat - s / n) > 1e-9:
            notes.append("recorded p_hat differs from successes/n")
        low = as_num(ci.get("low")) if ci else None
        high = as_num(ci.get("high")) if ci else None
        if available and (low is None or high is None):
            notes.append("confidence interval not recorded")
        failures = cal.get("failures") if isinstance(cal.get("failures"), dict) else {}
        point = {
            "date": date_of(cal), "created_at": cal.get("created_at"),
            "level": as_int(cal.get("level")), "n": n, "successes": s,
            "infra_errors": as_int(cal.get("infra_errors")),
            "failures": {str(k): v for k, v in sorted(failures.items())},
            "p_hat": p_hat if available else None,
            "difficulty": (1 - p_hat) if available else None,
            "ci_method": as_str(ci.get("method")) if ci else None,
            "ci_low": low if available else None, "ci_high": high if available else None,
            "available": available, "state": as_str(cal.get("state")),
            "selected": cal.get("selected") is True,
            "eligibility": as_str(cal.get("eligibility")),
            "contract_id": as_str(cal.get("contract_id")), "notes": notes,
            "record_ids": rids(cal)}
        panels.setdefault(pkey, []).append(point)
    out = []
    for pkey in sorted(panels, key=lambda k: tuple(str(x) for x in (k[0], k[1]) + k[2])):
        pts = panels[pkey]
        selected = None
        for p in pts:
            if p["selected"]:
                selected = p  # latest selected record in time order
        out.append({"profile_id": pkey[0], "reference_notebook_sha256": pkey[1],
                    "family_id": pkey[2][0], "generator_id": pkey[2][1],
                    "version": pkey[2][2],
                    "selected_level": selected["level"] if selected else None,
                    "selected_record_ids": selected["record_ids"] if selected else [],
                    "points": pts})
    return {"target": pview["curriculum"]["target"], "lo": pview["curriculum"]["lo"],
            "hi": pview["curriculum"]["hi"], "source": pview["curriculum_source"],
            "panels": out}


def derive_allocation(trials, contracts_by_id):
    rows = {}
    unknown_contracts = set()
    for t in trials:
        contract = contracts_by_id.get(t.get("contract_id"))
        if contract is None:
            unknown_contracts.add(as_str(t.get("contract_id")))
        epoch = as_str(contract.get("epoch_id")) if contract else None
        stage = as_str(t.get("stage"))
        group = STAGE_GROUPS.get(stage, "unknown")
        key = (epoch or "(unknown contract)", group, as_str(t.get("family_id")),
               as_str(t.get("generator_id")), as_int(t.get("version")), as_int(t.get("level")))
        row = rows.get(key)
        if row is None:
            row = {"epoch_id": key[0], "stage_group": group, "family_id": key[2],
                   "generator_id": key[3], "version": key[4], "level": key[5],
                   "trials": 0, "solved": 0, "unsolved": 0, "infra_error": 0,
                   "generation_error": 0, "other": 0, "first_date": date_of(t),
                   "last_date": date_of(t), "record_ids": []}
            rows[key] = row
        row["trials"] += 1
        outcome = t.get("outcome")
        row[outcome if outcome in ("solved", "unsolved", "infra_error") else "other"] += 1
        if t.get("reason") == "generation_error":
            row["generation_error"] += 1
        row["last_date"] = date_of(t)
        row["record_ids"].append(rid(t))
    planned = []
    for cid in sorted(contracts_by_id):
        c = contracts_by_id[cid]
        mixture = c.get("mixture") if isinstance(c.get("mixture"), list) else []
        tp = as_int(c.get("trials_planned"))
        for m in mixture:
            if not isinstance(m, dict):
                continue
            w = frac_of(m.get("weight"))
            planned.append({
                "contract_id": cid, "epoch_id": as_str(c.get("epoch_id")),
                "stage": as_str(c.get("stage")),
                "stage_group": STAGE_GROUPS.get(c.get("stage"), "unknown"),
                "family_id": as_str(m.get("family_id")),
                "generator_id": as_str(m.get("generator_id")),
                "version": as_int(m.get("version")), "level": as_int(m.get("level")),
                "weight": frac_str(w),
                "weight_value": float(w) if w is not None else None,
                "trials_planned": tp,
                "expected_trials": frac_str(w * tp) if (w is not None and tp is not None)
                else None,
                "record_ids": rids(c)})
    ordered = [rows[k] for k in sorted(rows, key=lambda k: tuple(
        "" if x is None else (("%09d" % x) if isinstance(x, int) else x) for x in k))]
    return {"rows": ordered, "planned": planned,
            "trials_with_unknown_contract": sorted(x for x in unknown_contracts if x)}


def contract_keys(contract):
    if contract is None:
        return None
    profile = contract.get("profile")
    mixture = contract.get("mixture")
    try:
        pdig = sha256_of(profile) if profile is not None else None
        mdig = sha256_of(mixture) if mixture is not None else None
    except (TypeError, ValueError):
        return None
    pid = profile.get("profile_id") if isinstance(profile, dict) else None
    model = profile.get("model") if isinstance(profile, dict) else None
    return {"profile_id": as_str(pid), "model": as_str(model), "profile_digest": pdig,
            "mixture_digest": mdig, "epoch_id": as_str(contract.get("epoch_id"))}


def comparison_row(cmp, contract):
    n = as_int(cmp.get("n"))
    inc_s = as_int(cmp.get("incumbent_successes"))
    cand_s = as_int(cmp.get("candidate_successes"))
    w, l = as_int(cmp.get("w")), as_int(cmp.get("l"))
    delta = as_num(cmp.get("delta_hat"))
    lb = as_num(cmp.get("lower_bound"))
    notes = []
    if n and w is not None and l is not None and delta is not None \
            and abs(delta - (w - l) / n) > 1e-9:
        notes.append("recorded delta_hat differs from (w-l)/n")
    if n and inc_s is not None and cand_s is not None and w is not None and l is not None \
            and cand_s - inc_s != w - l:
        notes.append("success counts inconsistent with w and l")
    if contract is None:
        notes.append("contract record not found")
    nb = cmp.get("notebook") if isinstance(cmp.get("notebook"), dict) else {}
    keys = contract_keys(contract) or {}
    verdict = as_str(cmp.get("verdict"))
    provisional = cmp.get("provisional") is True
    if verdict in PASS_VERDICTS:
        cls = "provisional" if provisional else "accepted"
    elif verdict == "fail":
        cls = "rejected"
    else:
        cls = "inconclusive"
    return {
        "date": date_of(cmp), "created_at": cmp.get("created_at"),
        "contract_id": as_str(cmp.get("contract_id")), "stage": as_str(cmp.get("stage")),
        "scope": as_str(cmp.get("scope")), "provisional": provisional, "verdict": verdict,
        "reason": as_str(cmp.get("reason")), "class": cls, "n": n,
        "incumbent_sha256": as_str(cmp.get("incumbent_sha256")),
        "candidate_sha256": as_str(cmp.get("candidate_sha256")),
        "pr": cmp.get("pr"), "head": as_str(cmp.get("head")),
        "incumbent_successes": inc_s, "candidate_successes": cand_s,
        "incumbent_rate": ratio(inc_s, n), "candidate_rate": ratio(cand_s, n),
        "w": w, "l": l, "both_solved": as_int(cmp.get("both_solved")),
        "both_failed": as_int(cmp.get("both_failed")),
        "delta_hat": delta, "delta_pp": None if delta is None else 100.0 * delta,
        "lower_bound": lb, "lower_bound_pp": None if lb is None else 100.0 * lb,
        "method": as_str(cmp.get("method")), "alpha": as_num(cmp.get("alpha")),
        "delta_ni": as_num(cmp.get("delta_ni")),
        "incumbent_bytes": as_int(nb.get("incumbent_bytes")),
        "incumbent_tokens": as_int(nb.get("incumbent_tokens")),
        "candidate_bytes": as_int(nb.get("candidate_bytes")),
        "candidate_tokens": as_int(nb.get("candidate_tokens")),
        "cap_tokens": as_int(nb.get("cap_tokens")),
        "tokenizer": as_str(nb.get("tokenizer")) if not isinstance(nb.get("tokenizer"), dict)
        else "%s v%s" % (nb["tokenizer"].get("kind"), nb["tokenizer"].get("version")),
        "policy_id": as_str(cmp.get("policy_id")), "epoch_id": as_str(cmp.get("epoch_id")),
        "anchor_epoch": as_str(cmp.get("anchor_epoch")),
        "profile_id": keys.get("profile_id"), "model": keys.get("model"),
        "profile_digest": keys.get("profile_digest"),
        "mixture_digest": keys.get("mixture_digest"),
        "usage": cmp.get("usage") if isinstance(cmp.get("usage"), dict) else None,
        "pair_count": len(cmp.get("pair_refs")) if isinstance(cmp.get("pair_refs"), list)
        else None,
        "notes": notes, "record_ids": rids(cmp, contract)}


def derive_activations(activations, issues):
    """Apply activations in sequence order with compare-and-swap; invalid events are reported."""
    chain = []
    active = None
    seen_seq = set()
    ordered = sorted(activations, key=lambda a: (
        as_int(a.get("sequence")) if as_int(a.get("sequence")) is not None else 1 << 62,
        a["_ts"], rid(a)))
    for a in ordered:
        seq = as_int(a.get("sequence"))
        problem = None
        if seq is None or seq < 1:
            problem = "activation without a valid sequence"
        elif seq in seen_seq:
            problem = "duplicate activation sequence %d" % seq
        elif a.get("predecessor_sha256") != active:
            problem = "activation predecessor does not match the active notebook " \
                      "(compare-and-swap)"
        if problem:
            issues.append({"file": "activations.jsonl", "line": None, "record_id": rid(a),
                           "problem": problem, "action": "excluded from the active chain"})
            continue
        seen_seq.add(seq)
        active = a.get("successor_sha256")
        chain.append(a)
    return chain, active


def notebook_sizes(contracts, comparisons):
    """hash -> list of observations {bytes, tokens, tokenizer, cap_tokens, record_ids}."""
    obs = {}
    for c in contracts:
        for arm in c.get("arms") if isinstance(c.get("arms"), list) else []:
            if isinstance(arm, dict) and isinstance(arm.get("notebook_sha256"), str):
                obs.setdefault(arm["notebook_sha256"], []).append({
                    "bytes": as_int(arm.get("notebook_bytes")),
                    "tokens": as_int(arm.get("notebook_tokens")), "tokenizer": None,
                    "cap_tokens": None, "record_ids": rids(c), "_ts": c["_ts"]})
    for cmp in comparisons:
        nb = cmp.get("notebook") if isinstance(cmp.get("notebook"), dict) else {}
        tok = nb.get("tokenizer")
        if isinstance(tok, dict):
            tok = "%s v%s" % (tok.get("kind"), tok.get("version"))
        for side in ("incumbent", "candidate"):
            h = cmp.get(side + "_sha256")
            if isinstance(h, str):
                obs.setdefault(h, []).append({
                    "bytes": as_int(nb.get(side + "_bytes")),
                    "tokens": as_int(nb.get(side + "_tokens")), "tokenizer": as_str(tok),
                    "cap_tokens": as_int(nb.get("cap_tokens")), "record_ids": rids(cmp),
                    "_ts": cmp["_ts"], "_cmp": rid(cmp)})
    return obs


def size_for(obs, h, prefer_ids=()):
    cands = obs.get(h) or []
    pref = [o for o in cands if o.get("_cmp") in prefer_ids]
    pool = pref or cands
    if not pool:
        return None
    best = sorted(pool, key=lambda o: o["_ts"])[-1]
    return {k: v for k, v in best.items() if not k.startswith("_")}


def derive_compression(chain, size_obs, comparisons_by_id, pview):
    rows = []
    for a in chain:
        cids = [c for c in a.get("comparison_ids") or [] if isinstance(c, str)]
        succ = a.get("successor_sha256")
        size = size_for(size_obs, succ, cids)
        rate, n, usage = None, None, None
        used = []
        for cid in cids:
            cmp = comparisons_by_id.get(cid)
            if cmp is None:
                continue
            used.append(cid)
            if cmp.get("candidate_sha256") == succ and as_int(cmp.get("n")):
                n = as_int(cmp.get("n"))
                rate = ratio(as_int(cmp.get("candidate_successes")), n)
                u = cmp.get("usage")
                usage = u.get("candidate") if isinstance(u, dict) else None
        tokens = size["tokens"] if size else None
        rows.append({
            "sequence": as_int(a.get("sequence")), "date": date_of(a),
            "created_at": a.get("created_at"), "reason": as_str(a.get("reason")),
            "scope": as_str(a.get("scope")), "provisional": a.get("provisional") is True,
            "predecessor_sha256": as_str(a.get("predecessor_sha256")),
            "successor_sha256": as_str(succ), "pr": a.get("pr"),
            "merge_commit": as_str(a.get("merge_commit")), "actor": as_str(a.get("actor")),
            "policy_id": as_str(a.get("policy_id")), "epoch_id": as_str(a.get("epoch_id")),
            "bytes": size["bytes"] if size else None, "tokens": tokens,
            "tokens_unavailable_reason": None if tokens is not None else (
                "no tokenizer measurement recorded" if size else "no size observation recorded"),
            "tokenizer": (size["tokenizer"] if size and size["tokenizer"] else pview["tokenizer"]),
            "cap_tokens": (size["cap_tokens"] if size and size["cap_tokens"] is not None
                           else pview["max_tokens"]),
            "cap_bytes": pview["max_bytes"],
            "comparison_ids": cids, "successor_success_rate": rate, "successor_n": n,
            "successor_usage_total": usage,
            "record_ids": rids(a) + [x for x in (size["record_ids"] if size else [])
                                     if x != rid(a)] + [c for c in used if c not in
                                                        (size["record_ids"] if size else [])]})
    return {"rows": rows}


def derive_performance(comparisons, contracts_by_id, chain):
    rows = [comparison_row(c, contracts_by_id.get(c.get("contract_id")))
            for c in comparisons if c.get("stage") not in ("anchor", "calibration")]
    events = [{"kind": "comparison", "date": r["date"], "created_at": r["created_at"],
               "ref": r} for r in rows]
    for a in chain:
        events.append({"kind": "activation", "date": date_of(a), "created_at": a["created_at"],
                       "ref": {"sequence": as_int(a.get("sequence")),
                               "reason": as_str(a.get("reason")),
                               "provisional": a.get("provisional") is True,
                               "successor_sha256": as_str(a.get("successor_sha256")),
                               "record_ids": rids(a)}})
    events.sort(key=lambda e: (e["created_at"], 0 if e["kind"] == "comparison" else 1,
                               e["ref"]["record_ids"][0]))
    ordered = []
    for i, e in enumerate(events, 1):
        item = dict(e["ref"])
        item["order"] = i
        item["kind"] = e["kind"]
        ordered.append(item)
    return {"points": ordered}


def derive_anchors(comparisons, contracts_by_id):
    groups = {}
    excluded = []
    for cmp in comparisons:
        if cmp.get("stage") != "anchor":
            continue
        contract = contracts_by_id.get(cmp.get("contract_id"))
        row = comparison_row(cmp, contract)
        if contract is None or row["anchor_epoch"] is None or row["profile_digest"] is None:
            excluded.append({"reason": "missing contract, anchor epoch or profile; "
                                       "comparability cannot be established",
                             "record_ids": row["record_ids"]})
            continue
        baseline = None
        for arm in contract.get("arms") if isinstance(contract.get("arms"), list) else []:
            if isinstance(arm, dict) and arm.get("arm") == "anchor_baseline":
                baseline = arm.get("notebook_sha256")
        reversed_ = baseline is not None and baseline == row["candidate_sha256"] \
            and baseline != row["incumbent_sha256"]
        n = row["n"]
        act_s = row["incumbent_successes"] if reversed_ else row["candidate_successes"]
        base_s = row["candidate_successes"] if reversed_ else row["incumbent_successes"]
        act_ci = wilson(act_s, n)
        base_ci = wilson(base_s, n)
        point = {
            "date": row["date"], "created_at": row["created_at"],
            "contract_id": row["contract_id"], "n": n,
            "available": bool(n) and act_s is not None and base_s is not None,
            "active_sha256": row["incumbent_sha256"] if reversed_ else row["candidate_sha256"],
            "baseline_sha256": row["candidate_sha256"] if reversed_ else row["incumbent_sha256"],
            "baseline_identified_by": "contract arm anchor_baseline" if baseline is not None
            else "assumed incumbent side (no anchor_baseline arm)",
            "active_successes": act_s, "baseline_successes": base_s,
            "active_rate": ratio(act_s, n), "baseline_rate": ratio(base_s, n),
            "active_ci": list(act_ci) if act_ci else None,
            "baseline_ci": list(base_ci) if base_ci else None,
            "ci_method": "wilson-95 (computed by the report from recorded counts)",
            "delta_pp": None if row["delta_pp"] is None else (
                -row["delta_pp"] if reversed_ else row["delta_pp"]),
            "lower_bound_pp": None if reversed_ else row["lower_bound_pp"],
            "verdict": row["verdict"], "notes": row["notes"],
            "record_ids": row["record_ids"]}
        gkey = (row["anchor_epoch"], row["profile_digest"], row["mixture_digest"])
        g = groups.get(gkey)
        if g is None:
            g = {"anchor_epoch": row["anchor_epoch"], "profile_id": row["profile_id"],
                 "model": row["model"], "profile_digest": row["profile_digest"],
                 "mixture_digest": row["mixture_digest"], "epoch_id": row["epoch_id"],
                 "points": []}
            groups[gkey] = g
        g["points"].append(point)
    ordered = sorted(groups.values(), key=lambda g: (g["points"][0]["created_at"],
                                                      g["anchor_epoch"], g["profile_digest"]))
    for i, g in enumerate(ordered):
        g["series_id"] = "anchor-series-%d" % (i + 1)
    return {"series": ordered, "excluded": excluded}


def derive_pareto(comparisons, contracts_by_id):
    groups = {}
    excluded = []
    for cmp in comparisons:
        if cmp.get("stage") in ("anchor", "calibration"):
            continue
        contract = contracts_by_id.get(cmp.get("contract_id"))
        row = comparison_row(cmp, contract)
        if contract is None or row["profile_digest"] is None or row["mixture_digest"] is None:
            excluded.append({"reason": "contract missing: profile and distribution unknown",
                             "record_ids": row["record_ids"]})
            continue
        if not row["n"]:
            excluded.append({"reason": "no completed pairs (n = 0)",
                             "record_ids": row["record_ids"]})
            continue
        gkey = (row["epoch_id"] or "", row["profile_digest"], row["mixture_digest"],
                row["scope"] or "")
        g = groups.setdefault(gkey, {
            "epoch_id": row["epoch_id"], "profile_id": row["profile_id"], "model": row["model"],
            "profile_digest": row["profile_digest"], "mixture_digest": row["mixture_digest"],
            "scope": row["scope"], "points": [], "excluded": []})
        for side in ("incumbent", "candidate"):
            tokens = row[side + "_tokens"]
            successes = row[side + "_successes"]
            pt = {"arm": side, "notebook_sha256": row[side + "_sha256"], "tokens": tokens,
                  "bytes": row[side + "_bytes"], "n": row["n"], "successes": successes,
                  "rate": ratio(successes, row["n"]),
                  "ci": list(wilson(successes, row["n"]) or []) or None,
                  "class": "incumbent" if side == "incumbent" else row["class"],
                  "verdict": row["verdict"], "stage": row["stage"], "date": row["date"],
                  "contract_id": row["contract_id"], "record_ids": row["record_ids"]}
            if tokens is None or pt["rate"] is None:
                g["excluded"].append({"reason": "token count unavailable (no tokenizer)"
                                      if tokens is None else "success rate unavailable",
                                      "arm": side, "record_ids": row["record_ids"]})
                continue
            g["points"].append(pt)
    out = []
    for gkey in sorted(groups):
        g = groups[gkey]
        eligible = [p for p in g["points"] if p["class"] in ("incumbent", "accepted",
                                                             "provisional")]
        frontier = []
        best = -1.0
        for p in sorted(eligible, key=lambda p: (p["tokens"], -p["rate"], p["record_ids"][0])):
            if p["rate"] > best:
                frontier.append(p)
                best = p["rate"]
        for p in g["points"]:
            p["on_frontier"] = any(p is f for f in frontier)
        g["frontier_record_ids"] = sorted({r for f in frontier for r in f["record_ids"]})
        out.append(g)
    for i, g in enumerate(out):
        g["group_id"] = "pareto-group-%d" % (i + 1)
    return {"groups": out, "excluded": excluded}


def usage_totals(trials):
    fields = ("model_calls", "input_tokens", "output_tokens", "reasoning_tokens",
              "cached_tokens", "wall_seconds", "lean_seconds")
    totals = {f: 0 for f in fields}
    missing = {f: 0 for f in fields}
    for t in trials:
        u = t.get("usage") if isinstance(t.get("usage"), dict) else {}
        for f in fields:
            v = as_num(u.get(f))
            if v is None:
                missing[f] += 1
            else:
                totals[f] += v
    return {"trials": len(trials), "totals": totals, "unavailable_counts": missing,
            "record_ids": [rid(t) for t in trials]}


def derive_role(role, records, pview, issues):
    pick = {k: [r for r in records[k] if r.get("role") == role] for k in ROLE_KINDS}
    contracts_by_id = {}
    for c in pick["contracts"]:
        cid = c.get("contract_id") or rid(c)
        contracts_by_id[cid] = c
    comparisons_by_id = {rid(c): c for c in pick["comparisons"]}
    chain, active = derive_activations(pick["activations"], issues)
    size_obs = notebook_sizes(pick["contracts"], pick["comparisons"])
    library = derive_library(pick["certifications"], pick["calibrations"])
    compression = derive_compression(chain, size_obs, comparisons_by_id, pview)
    performance = derive_performance(pick["comparisons"], contracts_by_id, chain)
    anchors = derive_anchors(pick["comparisons"], contracts_by_id)
    counts = {v: 0 for v in VERDICTS}
    counts["other"] = 0
    count_ids = []
    for c in pick["comparisons"]:
        v = c.get("verdict")
        counts[v if v in counts else "other"] += 1
        count_ids.append(rid(c))
    active_info = None
    if chain:
        last = compression["rows"][-1]
        active_info = {"sha256": active, "sequence": last["sequence"], "date": last["date"],
                       "reason": last["reason"], "provisional": last["provisional"],
                       "scope": last["scope"], "bytes": last["bytes"], "tokens": last["tokens"],
                       "tokens_unavailable_reason": last["tokens_unavailable_reason"],
                       "tokenizer": last["tokenizer"], "record_ids": last["record_ids"]}
    last_paired = None
    for p in performance["points"]:
        if p["kind"] == "comparison" and p["n"] and p["delta_pp"] is not None:
            last_paired = p
    last_anchor = None
    for g in anchors["series"]:
        for p in g["points"]:
            if p["available"] and (last_anchor is None
                                   or p["created_at"] >= last_anchor["created_at"]):
                last_anchor = dict(p, anchor_epoch=g["anchor_epoch"],
                                   profile_id=g["profile_id"])
    summary = dict(library["summary"])
    summary.update({
        "active_notebook": active_info,
        "activations_applied": len(chain),
        "evaluations_by_verdict": counts,
        "evaluations_pending": counts["awaiting_evaluator"],
        "evaluations_failed": counts["fail"] + counts["infra_error"],
        "evaluation_record_ids": count_ids,
        "last_comparable_paired_result": last_paired,
        "last_anchor_result": last_anchor,
        "usage": usage_totals(pick["trials"]),
        "record_counts": {k: len(v) for k, v in pick.items()}})
    return {
        "summary": summary,
        "library": {"points": library["points"]},
        "generators": {"rows": library["rows"]},
        "diversity": derive_diversity(pick["certifications"], pview),
        "difficulty": derive_difficulty(pick["calibrations"], pview),
        "allocation": derive_allocation(pick["trials"], contracts_by_id),
        "performance": performance,
        "compression": compression,
        "anchors": anchors,
        "pareto": derive_pareto(pick["comparisons"], contracts_by_id),
    }


def derive(records, issues, inputs, pview, as_of, generated_at):
    roles = {role: derive_role(role, records, pview, issues) for role in ROLES}
    return {
        "schema": REPORT_SCHEMA,
        "as_of": as_of.isoformat() if as_of else None,
        "generated_at": generated_at,
        "adversary_model": "classical",
        "adversary_statement": ADVERSARY_STATEMENT,
        "policy": {k: v for k, v in pview.items()},
        "inputs": inputs,
        "issues": issues,
        "roles": roles,
    }


# ---------------------------------------------------------------------------------------------
# Escaping
# ---------------------------------------------------------------------------------------------

def esc(value):
    return html.escape("" if value is None else str(value), quote=True)


_MD_SPECIAL = set("\\`*_{}[]()<>#!|~&\"'=:$")
_MD_SAFE_TOKEN = re.compile(r"[A-Za-z0-9][A-Za-z0-9:._/+-]*")


def md(value):
    """Markdown-escape untrusted text (one line; every markup character is backslash-escaped)."""
    text = "" if value is None else str(value)
    text = " ".join(text.split())
    out = "".join("\\" + ch if ch in _MD_SPECIAL else ch for ch in text)
    if out[:1] in ("-", "+", "."):
        out = "\\" + out
    return out


def md_id(value):
    """An identifier or hash as a code span when it is a plain token, else escaped text."""
    if isinstance(value, str) and _MD_SAFE_TOKEN.fullmatch(value):
        return "`%s`" % value
    return md(value)


def csv_cell(value):
    if value is None:
        return ""
    if isinstance(value, bool):
        return "true" if value else "false"
    if isinstance(value, (int, float)):
        return repr(value)
    if isinstance(value, (list, dict)):
        value = json.dumps(value, sort_keys=True, separators=(",", ":"))
    text = str(value)
    if text and text[0] in "=+-@\t\r\n|%":
        text = "'" + text
    return text


def json_for_script(obj):
    text = json.dumps(obj, sort_keys=True, ensure_ascii=True, allow_nan=False)
    return (text.replace("&", "\\u0026").replace("<", "\\u003c").replace(">", "\\u003e"))


# ---------------------------------------------------------------------------------------------
# SVG plotting
# ---------------------------------------------------------------------------------------------

def nice_ticks(lo, hi, count=5):
    if hi <= lo:
        hi = lo + 1
    span = hi - lo
    raw = span / count
    mag = 10 ** math.floor(math.log10(raw))
    step = mag
    for m in (1, 2, 2.5, 5, 10):
        if raw <= m * mag:
            step = m * mag
            break
    start = math.ceil(lo / step - 1e-9) * step
    ticks = []
    v = start
    while v <= hi + 1e-9:
        ticks.append(round(v, 10))
        v += step
    return ticks


def fmt_tick(v):
    if abs(v - round(v)) < 1e-9:
        return "%d" % round(v)
    return ("%.2f" % v).rstrip("0").rstrip(".")


class Plot:
    """A tiny deterministic SVG plot (one y axis)."""

    def __init__(self, plot_id, title, desc, x_domain, y_domain, x_label, y_label,
                 x_kind="time", x_labels=None, width=760, height=280):
        self.id = plot_id
        self.title = title
        self.desc = desc
        self.x0, self.x1 = x_domain
        if self.x1 <= self.x0:
            self.x0, self.x1 = self.x0 - 1, self.x1 + 1
        self.y0, self.y1 = y_domain
        if self.y1 <= self.y0:
            self.y1 = self.y0 + 1
        self.x_label, self.y_label = x_label, y_label
        self.x_kind = x_kind
        self.x_labels = x_labels or {}
        self.w, self.h = width, height
        self.ml, self.mr, self.mt, self.mb = 58, 44, 14, 46
        self.items = []

    def sx(self, x):
        return self.ml + (x - self.x0) / (self.x1 - self.x0) * (self.w - self.ml - self.mr)

    def sy(self, y):
        y = min(max(y, self.y0), self.y1)
        return self.h - self.mb - (y - self.y0) / (self.y1 - self.y0) * (
            self.h - self.mt - self.mb)

    def band(self, y_lo, y_hi, cls, label):
        top, bot = self.sy(y_hi), self.sy(y_lo)
        self.items.append('<rect class="%s" x="%.1f" y="%.1f" width="%.1f" height="%.1f">'
                          '<title>%s</title></rect>' % (
                              cls, self.ml, top, self.w - self.ml - self.mr, bot - top,
                              esc(label)))

    def hline(self, y, cls, label):
        yy = self.sy(y)
        self.items.append('<line class="%s" x1="%.1f" x2="%.1f" y1="%.1f" y2="%.1f">'
                          '<title>%s</title></line>' % (cls, self.ml, self.w - self.mr, yy, yy,
                                                        esc(label)))
        self.items.append('<text class="ann" x="%.1f" y="%.1f" text-anchor="end">%s</text>' % (
            self.w - self.mr - 2, yy - 3, esc(label)))

    def vline(self, x, cls, label, attrs=""):
        xx = self.sx(x)
        self.items.append('<g%s><line class="%s" x1="%.1f" x2="%.1f" y1="%.1f" y2="%.1f">'
                          '<title>%s</title></line><text class="ann" x="%.1f" y="%.1f">%s'
                          '</text></g>' % (attrs, cls, xx, xx, self.mt, self.h - self.mb,
                                           esc(label), xx + 3, self.mt + 10, esc(label)))

    def line(self, pts, cls, attrs=""):
        if len(pts) < 2:
            return
        d = " ".join("%s%.1f %.1f" % ("M" if i == 0 else "L", self.sx(x), self.sy(y))
                     for i, (x, y) in enumerate(pts))
        self.items.append('<path class="%s"%s d="%s"/>' % (cls, attrs, d))

    def errbar(self, x, y_lo, y_hi, cls, attrs=""):
        xx = self.sx(x)
        a, b = self.sy(y_lo), self.sy(y_hi)
        self.items.append('<path class="%s"%s d="M%.1f %.1fL%.1f %.1fM%.1f %.1fL%.1f %.1f'
                          'M%.1f %.1fL%.1f %.1f"/>' % (cls, attrs, xx, a, xx, b, xx - 4, a,
                                                       xx + 4, a, xx - 4, b, xx + 4, b))

    def point(self, x, y, shape, cls, tip, attrs=""):
        xx, yy = self.sx(x), self.sy(y)
        r = 4.5
        if shape == "square":
            mark = '<rect x="%.1f" y="%.1f" width="%.1f" height="%.1f"/>' % (
                xx - r, yy - r, 2 * r, 2 * r)
        elif shape == "diamond":
            mark = '<path d="M%.1f %.1fL%.1f %.1fL%.1f %.1fL%.1f %.1fZ"/>' % (
                xx, yy - r - 1, xx + r + 1, yy, xx, yy + r + 1, xx - r - 1, yy)
        elif shape == "cross":
            mark = '<path class="xmark" d="M%.1f %.1fL%.1f %.1fM%.1f %.1fL%.1f %.1f"/>' % (
                xx - r, yy - r, xx + r, yy + r, xx - r, yy + r, xx + r, yy - r)
        elif shape == "triangle":
            mark = '<path d="M%.1f %.1fL%.1f %.1fL%.1f %.1fZ"/>' % (
                xx, yy - r - 1, xx + r + 1, yy + r, xx - r - 1, yy + r)
        else:
            mark = '<circle cx="%.1f" cy="%.1f" r="%.1f"/>' % (xx, yy, r)
        self.items.append('<g class="pt %s"%s tabindex="0"><title>%s</title>'
                          '<circle class="hit" cx="%.1f" cy="%.1f" r="10"/>%s</g>' % (
                              cls, attrs, esc(tip), xx, yy, mark))

    def bar(self, x_lo, x_hi, y_lo, y_hi, cls, tip, attrs=""):
        a, b = self.sx(x_lo), self.sx(x_hi)
        top, bot = self.sy(y_hi), self.sy(y_lo)
        self.items.append('<rect class="bar %s"%s x="%.1f" y="%.1f" width="%.1f" '
                          'height="%.1f" rx="2"><title>%s</title></rect>' % (
                              cls, attrs, a, top, max(b - a, 1.0), max(bot - top, 0.0),
                              esc(tip)))

    def text(self, x, y, label, cls="ann", anchor="start"):
        self.items.append('<text class="%s" x="%.1f" y="%.1f" text-anchor="%s">%s</text>' % (
            cls, self.sx(x), self.sy(y), anchor, esc(label)))

    def render(self):
        out = ['<svg class="chart" viewBox="0 0 %d %d" role="img" aria-labelledby="%s-t %s-d">'
               % (self.w, self.h, self.id, self.id)]
        out.append('<title id="%s-t">%s</title><desc id="%s-d">%s</desc>' % (
            self.id, esc(self.title), self.id, esc(self.desc)))
        for t in nice_ticks(self.y0, self.y1):
            yy = self.sy(t)
            out.append('<line class="grid" x1="%.1f" x2="%.1f" y1="%.1f" y2="%.1f"/>'
                       '<text class="tick" x="%.1f" y="%.1f" text-anchor="end">%s</text>' % (
                           self.ml, self.w - self.mr, yy, yy, self.ml - 6, yy + 4, fmt_tick(t)))
        base = self.h - self.mb
        out.append('<line class="axis" x1="%.1f" x2="%.1f" y1="%.1f" y2="%.1f"/>' % (
            self.ml, self.w - self.mr, base, base))
        if self.x_kind == "time":
            ticks = []
            n = 5
            for i in range(n + 1):
                ticks.append(self.x0 + (self.x1 - self.x0) * i / n)
            last = None
            for t in ticks:
                label = (_EPOCH + datetime.timedelta(days=t)).strftime("%Y-%m-%d")
                if label == last:
                    continue
                last = label
                out.append('<text class="tick" x="%.1f" y="%.1f" text-anchor="middle">%s'
                           '</text>' % (self.sx(t), base + 16, label))
        else:
            labels = self.x_labels
            if self.x_kind == "linear":
                labels = {t: fmt_tick(t) for t in nice_ticks(self.x0, self.x1)
                          if self.x0 <= t <= self.x1}
            keys = sorted(labels)
            stride = max(1, int(math.ceil(len(keys) / 14.0)))
            for i, k in enumerate(keys):
                if i % stride:
                    continue
                out.append('<text class="tick" x="%.1f" y="%.1f" text-anchor="middle">%s'
                           '</text>' % (self.sx(k), base + 16, esc(labels[k])))
        out.append('<text class="axlabel" x="%.1f" y="%.1f" text-anchor="middle">%s</text>' % (
            (self.ml + self.w - self.mr) / 2, self.h - 8, esc(self.x_label)))
        out.append('<text class="axlabel" transform="translate(14 %.1f) rotate(-90)" '
                   'text-anchor="middle">%s</text>' % ((self.mt + base) / 2, esc(self.y_label)))
        out.extend(self.items)
        out.append("</svg>")
        return "".join(out)


def time_domain(dates):
    days = [day_number(datetime.datetime.strptime(d, "%Y-%m-%d").replace(
        tzinfo=datetime.timezone.utc)) for d in dates]
    if not days:
        return (0, 1)
    lo, hi = min(days), max(days)
    pad = max(1.0, (hi - lo) * 0.05)
    return (lo - pad, hi + pad)


def dnum(rowdate):
    return day_number(datetime.datetime.strptime(rowdate, "%Y-%m-%d").replace(
        tzinfo=datetime.timezone.utc))


# ---------------------------------------------------------------------------------------------
# HTML rendering
# ---------------------------------------------------------------------------------------------

FILTER_DIMS = ("family", "generator", "profile", "epoch", "scope", "notebook")


def fattrs(**kw):
    parts = []
    for k in FILTER_DIMS + ("date",):
        v = kw.get(k)
        if v is not None and v != "":
            parts.append(' data-f-%s="%s"' % (k, esc(v)))
    return "".join(parts)


def ids_cell(ids):
    if not ids:
        return "<td></td>"
    inner = "<br>".join('<code title="%s">%s</code>' % (esc(i), esc(short(i))) for i in ids[:4])
    if len(ids) > 4:
        inner += "<br><span class=\"muted\">+%d more (see data.json)</span>" % (len(ids) - 4)
    return "<td>%s</td>" % inner


def table(caption, headers, rows):
    """rows: list of (attrs, [cell html...], record_ids)."""
    if not rows:
        return '<p class="empty">No observations.</p>'
    out = ['<div class="tablewrap"><table><caption>%s</caption><thead><tr>' % esc(caption)]
    out.extend('<th scope="col">%s</th>' % esc(h) for h in headers + ["Records"])
    out.append("</tr></thead><tbody>")
    for attrs, cells, ids in rows:
        out.append("<tr%s>%s%s</tr>" % (attrs, "".join("<td>%s</td>" % c for c in cells),
                                        ids_cell(ids)))
    out.append("</tbody></table></div>")
    return "".join(out)


def fmt(v, unit=""):
    if v is None:
        return '<span class="muted">n/a</span>'
    if isinstance(v, bool):
        return "yes" if v else "no"
    if isinstance(v, float):
        return esc("%.3f%s" % (v, unit))
    return esc("%s%s" % (v, unit))


def code(v):
    if v is None:
        return '<span class="muted">n/a</span>'
    return '<code title="%s">%s</code>' % (esc(v), esc(short(v)))


def section(sec_id, title, caption, body):
    return ('<section class="chartsec" id="%s"><h3>%s</h3><p class="caption">%s</p>%s'
            '</section>' % (esc(sec_id), esc(title), caption, body))


def render_library(role, d):
    pts = d["library"]["points"]
    if not pts:
        return section(role + "-library", "Generator library growth",
                       "Cumulative certified generators, versions and families.",
                       '<p class="empty">No observations: no certification records.</p>')
    xs = [dnum(p["date"]) for p in pts]
    ymax = max(max(p["certified_versions"], p["unique_generators"], p["families"]) for p in pts)
    plot = Plot(role + "-lib", "Generator library growth (%s)" % role,
                "Cumulative counts after each certification event.",
                time_domain([p["date"] for p in pts]), (0, max(1, ymax) * 1.1 + 0.5),
                "certification date (UTC)", "count")
    series = (("certified_versions", "k1", "square", "certified versions"),
              ("unique_generators", "k2", "circle", "unique generator IDs"),
              ("families", "k3", "diamond", "distinct families"))
    for key, cls, shape, label in series:
        step = []
        for x, p in zip(xs, pts):
            if step:
                step.append((x, step[-1][1]))
            step.append((x, p[key]))
        plot.line(step, "ln " + cls)
        for x, p in zip(xs, pts):
            plot.point(x, p[key], shape, cls,
                       "%s: %d on %s after %s of %s (record %s)" % (
                           label, p[key], p["date"], p["event"],
                           vlabel((p["family_id"], p["generator_id"], p["version"])),
                           short(p["record_ids"][0])),
                       fattrs(family=p["family_id"], generator=p["generator_id"], date=p["date"]))
    legend = legend_html([("k1", "square", "certified versions (cumulative)"),
                          ("k2", "circle", "unique generator IDs (cumulative)"),
                          ("k3", "diamond", "distinct approved families (cumulative)")])
    rows = []
    for p in pts:
        c = p["current_status_counts"]
        rows.append((fattrs(family=p["family_id"], generator=p["generator_id"], date=p["date"]),
                     [esc(p["date"]), esc(p["event"]),
                      esc(vlabel((p["family_id"], p["generator_id"], p["version"]))),
                      fmt(p["certified_versions"]), fmt(p["unique_generators"]),
                      fmt(p["families"]), fmt(c["certified"]), fmt(c["quarantined"]),
                      fmt(c["superseded"]), fmt(c["rejected"])], p["record_ids"]))
    body = plot.render() + legend + table(
        "Certification events and cumulative counts",
        ["Date", "Event", "Generator version", "Certified versions", "Unique generators",
         "Families", "Now certified", "Now quarantined", "Now superseded", "Rejected"], rows)
    return section(role + "-library", "Generator library growth",
                   "Cumulative <b>certified</b> versions, unique generator IDs and approved "
                   "families (versions are not new generators; rejected or draft versions are "
                   "never counted). Current-state columns count each version by its latest "
                   "status.", body)


def legend_html(entries):
    out = ['<ul class="legend">']
    for cls, shape, label in entries:
        out.append('<li><svg width="18" height="14" aria-hidden="true"><g class="pt %s">%s</g>'
                   '</svg>%s</li>' % (cls, {
                       "square": '<rect x="4" y="2" width="10" height="10"/>',
                       "diamond": '<path d="M9 1L15 7L9 13L3 7Z"/>',
                       "cross": '<path class="xmark" d="M4 2L14 12M4 12L14 2"/>',
                       "triangle": '<path d="M9 1L15 13L3 13Z"/>',
                       "line": '<line x1="1" x2="17" y1="7" y2="7"/>',
                       "dash": '<line class="dash" x1="1" x2="17" y1="7" y2="7"/>',
                       "band": '<rect class="bandsw" x="1" y="2" width="16" height="10"/>'}.get(
                           shape, '<circle cx="9" cy="7" r="5"/>'), esc(label)))
    out.append("</ul>")
    return "".join(out)


def render_diversity(role, d):
    panels = d["diversity"]["panels"]
    title = "Certified diversity"
    caption = ("Seed bits <i>k</i> and the <b>certified lower bound</b> <i>h</i> on semantic "
               "min-entropy (bits) against the required threshold, one panel per family; lines "
               "break when the equivalence definition or family revision changes. <i>h</i> is a "
               "lower bound, not the actual entropy, and is never summed across families. It is "
               "unrelated to the empirical success rates below.")
    if not panels:
        return section(role + "-diversity", title, caption,
                       '<p class="empty">No observations: no certified generator versions.</p>')
    body = []
    for i, panel in enumerate(panels):
        pts = [p for s in panel["segments"] for p in s["points"]]
        vals = [v for p in pts for v in (p["seed_bits"], p["certified_lower_bound_bits"],
                                         p["required_bits"]) if v is not None]
        plot = Plot("%s-div-%d" % (role, i), "Certified diversity: family %s" % panel["family_id"],
                    "Seed bits, certified entropy lower bound and required bits per version.",
                    time_domain([p["date"] for p in pts]), (0, max(vals + [1]) * 1.15),
                    "certification date (UTC)", "bits")
        for sidx, seg in enumerate(panel["segments"]):
            sp = seg["points"]
            for key, cls in (("seed_bits", "ln k0"), ("certified_lower_bound_bits", "ln cert"),
                             ("required_bits", "ln req dash")):
                plot.line([(dnum(p["date"]), p[key]) for p in sp if p[key] is not None], cls)
            if sidx > 0:
                plot.vline(dnum(sp[0]["date"]) - 0.3, "boundary",
                           "equivalence/revision change")
            for p in sp:
                fa = fattrs(family=panel["family_id"], generator=p["generator_id"], date=p["date"])
                tip = "%s v%s on %s: k=%s bits, certified h>=%s bits, required %s bits (%s)" % (
                    p["generator_id"], p["version"], p["date"], p["seed_bits"],
                    p["certified_lower_bound_bits"], p["required_bits"],
                    short(p["record_ids"][0]))
                if p["seed_bits"] is not None:
                    plot.point(dnum(p["date"]), p["seed_bits"], "square", "k0", tip, fa)
                if p["certified_lower_bound_bits"] is not None:
                    plot.point(dnum(p["date"]), p["certified_lower_bound_bits"], "circle", "cert",
                               tip, fa)
                if p["required_bits"] is not None:
                    plot.point(dnum(p["date"]), p["required_bits"], "triangle", "req", tip, fa)
        body.append('<h4>Family <code>%s</code></h4>' % esc(panel["family_id"]))
        body.append(plot.render())
        rows = []
        for sidx, seg in enumerate(panel["segments"]):
            for p in seg["points"]:
                rows.append((fattrs(family=panel["family_id"], generator=p["generator_id"],
                                    date=p["date"]),
                             [esc(p["date"]), esc("%s v%s" % (p["generator_id"], p["version"])),
                              fmt(p["seed_bits"], " bits"),
                              fmt(p["certified_lower_bound_bits"], " bits"),
                              fmt(p["required_bits"], " bits"), fmt(p["h_over_k"]),
                              "%d" % (sidx + 1), code(p["equivalence"]),
                              code(p["family_revision"])], p["record_ids"]))
        body.append(table("Certified diversity, family %s" % panel["family_id"],
                          ["Date", "Generator version", "Seed bits k",
                           "Certified lower bound h", "Required h", "h/k", "Segment",
                           "Equivalence", "Family revision"], rows))
    body.insert(0, legend_html([("k0", "square", "seed bits k (parameter)"),
                                ("cert", "circle", "certified lower bound h (certified)"),
                                ("req", "triangle", "required threshold (policy)")]))
    return section(role + "-diversity", title, caption, "".join(body))


def render_difficulty(role, d):
    diff = d["difficulty"]
    caption = ("Empirical reference-agent success rate p with Wilson 95%% interval and sample size; "
               "shaded: preferred interval [%s, %s]; dashed: target %s (%s). "
               "%s. One panel per generator version and reference profile/notebook; n = 0 is "
               "shown as unavailable, never as 0%%. Hollow marks are stale calibrations; a ring "
               "marks the selected level." % (esc(diff["lo"]), esc(diff["hi"]),
                                             esc(diff["target"]), esc(diff["source"]),
                                             esc(DIFFICULTY_CAPTION)))
    if not diff["panels"]:
        return section(role + "-difficulty", "Difficulty evolution", caption,
                       '<p class="empty">No observations: no calibration records.</p>')
    lo, hi, target = (float(Fraction(diff[k])) for k in ("lo", "hi", "target"))
    body = [legend_html([("old", "circle", "fresh calibration (empirical)"),
                         ("old hollow", "circle", "stale calibration"),
                         ("old sel", "circle", "selected level"),
                         ("band", "band", "preferred interval"),
                         ("tgt", "dash", "target")])]
    for i, panel in enumerate(diff["panels"]):
        pts = panel["points"]
        levels = sorted({p["level"] for p in pts if p["level"] is not None})
        plot = Plot("%s-diff-%d" % (role, i),
                    "Difficulty: %s, profile %s" % (vlabel((panel["family_id"],
                                                            panel["generator_id"],
                                                            panel["version"])),
                                                    panel["profile_id"]),
                    "Success rate per level over time with Wilson intervals.",
                    time_domain([p["date"] for p in pts]), (0, 100),
                    "calibration date (UTC)", "success rate (%)")
        plot.band(lo * 100, hi * 100, "band", "preferred interval")
        plot.hline(target * 100, "tgt dash", "target %s%%" % fmt_tick(target * 100))
        fa_base = dict(family=panel["family_id"], generator="%s v%s" % (
            panel["generator_id"], panel["version"]), profile=panel["profile_id"],
            notebook=panel["reference_notebook_sha256"])
        for lv in levels:
            lp = [p for p in pts if p["level"] == lv]
            cls = "k%d" % (1 + (levels.index(lv) % 8))
            seg = []
            for p in lp:
                if not p["available"]:
                    plot.line(seg, "ln " + cls)
                    seg = []
                    continue
                seg.append((dnum(p["date"]), p["p_hat"] * 100))
            plot.line(seg, "ln " + cls)
            for p in lp:
                fa = fattrs(date=p["date"], **fa_base)
                if not p["available"]:
                    plot.text(dnum(p["date"]), 2, "L%s n/a (n=0)" % lv, "ann", "middle")
                    continue
                if p["ci_low"] is not None and p["ci_high"] is not None:
                    plot.errbar(dnum(p["date"]), p["ci_low"] * 100, p["ci_high"] * 100,
                                "eb " + cls, fa)
                extra = (" hollow" if p["state"] == "stale" else "") + (
                    " sel" if p["selected"] else "")
                plot.point(dnum(p["date"]), p["p_hat"] * 100, "circle", cls + extra,
                           "level %s on %s: %d/%d solved = %s (CI %s to %s), %s, %s%s" % (
                               lv, p["date"], p["successes"] or 0, p["n"], pct(p["p_hat"]),
                               pct(p["ci_low"]), pct(p["ci_high"]), p["state"],
                               p["eligibility"], ", selected" if p["selected"] else ""), fa)
            last = [p for p in lp if p["available"]]
            if last:
                plot.text(dnum(last[-1]["date"]), last[-1]["p_hat"] * 100 + 4, "L%s" % lv)
        body.append('<h4>%s &middot; profile <code>%s</code> &middot; reference notebook %s '
                    '&middot; selected level: %s</h4>' % (
                        esc(vlabel((panel["family_id"], panel["generator_id"],
                                    panel["version"]))),
                        esc(panel["profile_id"]), code(panel["reference_notebook_sha256"]),
                        esc(panel["selected_level"]) if panel["selected_level"] is not None
                        else '<span class="muted">none</span>'))
        body.append(plot.render())
        body.append(legend_html([("k%d" % (1 + (i2 % 8)), "circle", "level L%s" % lv)
                                 for i2, lv in enumerate(levels)]))
        rows = []
        for p in pts:
            rows.append((fattrs(date=p["date"], **fa_base),
                         [esc(p["date"]), fmt(p["level"]), fmt(p["n"]), fmt(p["successes"]),
                          esc(pct(p["p_hat"])) if p["available"]
                          else '<span class="unavail">unavailable (n=0)</span>',
                          esc("%s to %s" % (pct(p["ci_low"]), pct(p["ci_high"])))
                          if p["available"] else "n/a",
                          esc(pct(p["difficulty"])) if p["available"] else "n/a",
                          fmt(p["infra_errors"]), esc(p["state"]), esc(p["eligibility"]),
                          "yes" if p["selected"] else "no", esc("; ".join(p["notes"]))],
                         p["record_ids"]))
        body.append(table("Calibrations", ["Date", "Level", "n", "Successes", "Success rate",
                                           "Wilson 95% CI", "Difficulty 1-p", "Infra errors",
                                           "State", "Eligibility", "Selected", "Notes"], rows))
    return section(role + "-difficulty", "Difficulty evolution", caption, "".join(body))


def render_allocation(role, d):
    al = d["allocation"]
    caption = ("Evaluated task counts (trials) per epoch and family, split into exploration "
               "(calibration), promotion (screen/confirm), anchor and transfer, with invalid "
               "(infrastructure or generation error) counts; planned mixture weights below.")
    if not al["rows"] and not al["planned"]:
        return section(role + "-allocation", "Curriculum allocation", caption,
                       '<p class="empty">No observations: no trials or contracts.</p>')
    body = []
    if al["rows"]:
        bars = {}
        for r in al["rows"]:
            k = (r["epoch_id"], r["family_id"] or "")
            bars.setdefault(k, {}).setdefault(r["stage_group"], [0, 0, []])
            cell = bars[k][r["stage_group"]]
            cell[0] += r["trials"]
            cell[1] += r["infra_error"] + r["generation_error"]
            cell[2].extend(r["record_ids"])
        keys = sorted(bars)
        labels = {i: "%s | %s" % (short(k[0], 10), short(k[1], 10)) for i, k in enumerate(keys)}
        ymax = max(sum(v[0] for v in b.values()) for b in bars.values())
        plot = Plot(role + "-alloc", "Curriculum allocation (%s)" % role,
                    "Stacked trial counts per epoch and family by stage group.",
                    (-0.6, len(keys) - 0.4), (0, ymax * 1.15 + 1), "epoch | family",
                    "trials (count)", x_kind="ordinal", x_labels=labels)
        for i, k in enumerate(keys):
            y = 0
            for gi, g in enumerate(STAGE_GROUP_ORDER):
                if g not in bars[k]:
                    continue
                cnt, bad, _ids = bars[k][g]
                plot.bar(i - 0.3, i + 0.3, y, y + cnt, "g%d" % gi,
                         "%s, family %s, %s: %d trials (%d invalid)" % (k[0], k[1], g, cnt, bad),
                         fattrs(epoch=k[0], family=k[1]))
                y += cnt
            plot.text(i, y + ymax * 0.03, "%d" % y, "ann", "middle")
        body.append(plot.render())
        body.append(legend_html([("g%d" % i, "square", g)
                                 for i, g in enumerate(STAGE_GROUP_ORDER)]))
        rows = []
        for r in al["rows"]:
            rows.append((fattrs(epoch=r["epoch_id"], family=r["family_id"],
                                generator=r["generator_id"], date=r["last_date"]),
                         [esc(r["epoch_id"]), esc(r["stage_group"]),
                          esc(vlabel((r["family_id"], r["generator_id"], r["version"]))),
                          fmt(r["level"]), fmt(r["trials"]), fmt(r["solved"]),
                          fmt(r["unsolved"]), fmt(r["infra_error"]),
                          fmt(r["generation_error"]),
                          esc("%s to %s" % (r["first_date"], r["last_date"]))],
                         r["record_ids"]))
        body.append(table("Evaluated tasks", ["Epoch", "Split", "Generator version", "Level",
                                              "Trials", "Solved", "Unsolved", "Infra errors",
                                              "Generation errors", "Dates"], rows))
    if al["trials_with_unknown_contract"]:
        body.append('<p class="warn">Trials reference contracts not present in the records: %s'
                    '</p>' % ", ".join(code(c) for c in al["trials_with_unknown_contract"]))
    prow = []
    for p in al["planned"]:
        prow.append((fattrs(epoch=p["epoch_id"], family=p["family_id"],
                            generator=p["generator_id"]),
                     [code(p["contract_id"]), esc(p["epoch_id"]), esc(p["stage"]),
                      esc(vlabel((p["family_id"], p["generator_id"], p["version"]))),
                      fmt(p["level"]), fmt(p["weight"]), fmt(p["trials_planned"]),
                      fmt(p["expected_trials"])], p["record_ids"]))
    body.append(table("Frozen mixture weights per contract",
                      ["Contract", "Epoch", "Stage", "Generator version", "Level", "Weight",
                       "Trials planned", "Expected trials"], prow))
    return section(role + "-allocation", "Curriculum allocation", caption, "".join(body))


def cmp_tip(p):
    return ("%s %s (%s%s), n=%s: incumbent %s, candidate %s, delta %s, lower bound %s, "
            "verdict %s (%s); contract %s" % (
                p["date"], p["stage"], p["scope"], ", provisional" if p["provisional"] else "",
                p["n"], pct(p["incumbent_rate"]), pct(p["candidate_rate"]), pp(p["delta_pp"]),
                pp(p["lower_bound_pp"]), p["verdict"], p["reason"], short(p["contract_id"])))


CLASS_STYLE = {"accepted": ("emp", "circle"), "provisional": ("prov hollow", "diamond"),
               "rejected": ("rej", "cross"), "inconclusive": ("inc", "triangle")}


def render_performance(role, d):
    pts = d["performance"]["points"]
    caption = ("Each paired comparison is a separate point in record order (no line: contracts "
               "differ). Top: incumbent (old) and candidate (new) <b>empirical</b> success rates. "
               "Bottom: paired difference in percentage points with the recorded one-sided lower "
               "bound (whisker). Vertical lines are activation events. Rejected and inconclusive "
               "candidates are shown. n = 0 (awaiting evaluator) is unavailable, not zero.")
    if not pts:
        return section(role + "-performance", "Notebook performance", caption,
                       '<p class="empty">No observations: no comparisons or activations.</p>')
    labels = {p["order"]: str(p["order"]) for p in pts}
    dom = (0.4, len(pts) + 0.6)
    top = Plot(role + "-perf", "Notebook performance (%s)" % role,
               "Old and new success rates per comparison.", dom, (0, 100),
               "event order", "success rate (%)", x_kind="ordinal", x_labels=labels)
    deltas = [v for p in pts if p["kind"] == "comparison"
              for v in (p["delta_pp"], p["lower_bound_pp"]) if v is not None]
    lo_d = min(deltas + [-10.0])
    hi_d = max(deltas + [10.0])
    bot = Plot(role + "-perf-delta", "Paired difference (%s)" % role,
               "Paired delta and lower bound per comparison.", dom,
               (math.floor(lo_d / 10) * 10, math.ceil(hi_d / 10) * 10), "event order",
               "candidate \u2212 incumbent (pp)", x_kind="ordinal", x_labels=labels)
    bot.hline(0, "zero", "0 pp")
    for p in pts:
        x = p["order"]
        if p["kind"] == "activation":
            label = "act #%s %s%s" % (p["sequence"], p["reason"],
                                      " (prov.)" if p["provisional"] else "")
            fa = fattrs(notebook=p["successor_sha256"])
            top.vline(x, "act", label, fa)
            bot.vline(x, "act", label, fa)
            continue
        fa = fattrs(scope=p["scope"], epoch=p["epoch_id"], profile=p["profile_id"],
                    notebook=p["candidate_sha256"], date=p["date"])
        cls, shape = CLASS_STYLE[p["class"]]
        if p["incumbent_rate"] is None:
            top.text(x, 3, "n/a", "ann", "middle")
            continue
        top.point(x - 0.12, p["incumbent_rate"] * 100, "square", "old hollow", cmp_tip(p), fa)
        top.point(x + 0.12, p["candidate_rate"] * 100, shape, cls, cmp_tip(p), fa)
        if p["delta_pp"] is not None:
            if p["lower_bound_pp"] is not None:
                bot.errbar(x, p["lower_bound_pp"], p["delta_pp"], "eb " + cls.split()[0], fa)
            bot.point(x, p["delta_pp"], shape, cls, cmp_tip(p), fa)
    body = [legend_html([("old hollow", "square", "incumbent (old) rate"),
                         ("emp", "circle", "candidate: passed (normal)"),
                         ("prov hollow", "diamond", "candidate: passed provisionally"),
                         ("rej", "cross", "candidate: rejected (fail)"),
                         ("inc", "triangle", "candidate: inconclusive / stale / infra error")]),
            top.render(), bot.render()]
    rows = []
    for p in pts:
        if p["kind"] == "activation":
            rows.append((fattrs(notebook=p["successor_sha256"]),
                         [fmt(p["order"]), "activation", esc("#%s %s" % (p["sequence"],
                                                                         p["reason"])),
                          "", "", "", "", "", "", "", "provisional" if p["provisional"] else "",
                          code(p["successor_sha256"])], p["record_ids"]))
            continue
        rows.append((fattrs(scope=p["scope"], epoch=p["epoch_id"], profile=p["profile_id"],
                            notebook=p["candidate_sha256"], date=p["date"]),
                     [fmt(p["order"]), esc(p["date"]),
                      esc("%s / %s" % (p["stage"], p["verdict"])), esc(p["reason"]),
                      fmt(p["n"]), esc(pct(p["incumbent_rate"])),
                      esc(pct(p["candidate_rate"])),
                      esc("w=%s l=%s" % (p["w"], p["l"])), esc(pp(p["delta_pp"])),
                      esc(pp(p["lower_bound_pp"])),
                      esc("%s%s" % (p["scope"], " (provisional)" if p["provisional"] else "")),
                      code(p["candidate_sha256"]) + ("<br>" + esc("; ".join(p["notes"]))
                                                     if p["notes"] else "")],
                     p["record_ids"]))
    body.append(table("Comparisons and activations",
                      ["#", "Date", "Stage / verdict", "Reason", "Pairs n", "Old rate",
                       "New rate", "Discordant", "Delta", "Lower bound", "Scope", "Notebook"],
                      rows))
    return section(role + "-performance", "Notebook performance", caption, "".join(body))


def render_compression(role, d):
    rows_d = d["compression"]["rows"]
    caption = ("Size of each activated notebook in activation order: tokens (with the tokenizer "
               "named) and bytes, against the configured caps. Missing tokenizer measurements "
               "are labelled, not drawn as zero.")
    if not rows_d:
        return section(role + "-compression", "Notebook compression", caption,
                       '<p class="empty">No observations: no activations.</p>')
    labels = {r["sequence"]: "#%s" % r["sequence"] for r in rows_d}
    dom = (min(labels) - 0.6, max(labels) + 0.6)
    body = []
    for unit, key, cap_key in (("tokens", "tokens", "cap_tokens"),
                               ("bytes", "bytes", "cap_bytes")):
        vals = [r[key] for r in rows_d if r[key] is not None]
        caps = [r[cap_key] for r in rows_d if r[cap_key] is not None]
        plot = Plot("%s-comp-%s" % (role, unit), "Notebook %s (%s)" % (unit, role),
                    "Activated notebook %s per activation." % unit, dom,
                    (0, max(vals + caps + [1]) * 1.15), "activation sequence",
                    "%s (count)" % unit, x_kind="ordinal", x_labels=labels)
        if caps:
            plot.hline(caps[-1], "cap dash", "cap %d %s" % (caps[-1], unit))
        for r in rows_d:
            fa = fattrs(notebook=r["successor_sha256"], scope=r["scope"], date=r["date"],
                        epoch=r["epoch_id"])
            if r[key] is None:
                plot.text(r["sequence"], (max(vals + caps + [1]) * 0.05),
                          "n/a: %s" % (r["tokens_unavailable_reason"] if key == "tokens"
                                       else "no size recorded"), "ann", "middle")
                continue
            cls = "prov hollowbar" if r["provisional"] else "old"
            plot.bar(r["sequence"] - 0.3, r["sequence"] + 0.3, 0, r[key], cls,
                     "activation #%s (%s): %d %s%s" % (r["sequence"], r["reason"], r[key], unit,
                                                       ", provisional" if r["provisional"]
                                                       else ""), fa)
        body.append(plot.render())
    body.insert(0, legend_html([("old", "square", "activated notebook (measured size)"),
                                ("prov hollowbar", "square", "provisionally activated"),
                                ("cap", "dash", "configured cap")]))
    rows = []
    for r in rows_d:
        usage = r["successor_usage_total"]
        rows.append((fattrs(notebook=r["successor_sha256"], scope=r["scope"], date=r["date"],
                            epoch=r["epoch_id"]),
                     [fmt(r["sequence"]), esc(r["date"]), esc(r["reason"]),
                      esc("%s%s" % (r["scope"] or "n/a",
                                    " (provisional)" if r["provisional"] else "")),
                      code(r["successor_sha256"]),
                      fmt(r["tokens"]) if r["tokens"] is not None
                      else '<span class="unavail">%s</span>' % esc(r["tokens_unavailable_reason"]),
                      fmt(r["bytes"]), fmt(r["tokenizer"]), fmt(r["cap_tokens"]),
                      fmt(r["cap_bytes"]),
                      esc(pct(r["successor_success_rate"])) + (
                          " (n=%d)" % r["successor_n"] if r["successor_n"] else ""),
                      esc(json.dumps(usage, sort_keys=True)) if usage is not None
                      else '<span class="muted">not measured</span>'],
                     r["record_ids"]))
    body.append(table("Activated notebooks", [
        "Seq", "Date", "Reason", "Scope", "Notebook", "Tokens", "Bytes", "Tokenizer",
        "Token cap", "Byte cap", "Paired success rate", "Recorded usage (totals over n)"], rows))
    return section(role + "-compression", "Notebook compression", caption, "".join(body))


def render_anchors(role, d):
    an = d["anchors"]
    caption = ("The main longitudinal chart: active-generation notebook versus the frozen "
               "baseline on fresh seeds from one fixed anchor distribution. One panel per anchor "
               "epoch and exact profile; lines never cross a panel boundary and scores from "
               "different profiles are never spliced. Intervals are Wilson 95% computed from the "
               "recorded counts.")
    if not an["series"]:
        body = '<p class="empty">No observations: no comparable anchor comparisons.</p>'
        if an["excluded"]:
            body += excluded_html(an["excluded"])
        return section(role + "-anchor", "Anchor learning curve", caption, body)
    body = [legend_html([("emp", "circle", "active notebook (empirical)"),
                         ("base", "square", "frozen baseline (empirical)")])]
    for i, g in enumerate(an["series"]):
        pts = g["points"]
        plot = Plot("%s-anchor-%d" % (role, i),
                    "Anchor epoch %s, profile %s" % (g["anchor_epoch"], g["profile_id"]),
                    "Active and baseline success rates within one anchor epoch.",
                    time_domain([p["date"] for p in pts]), (0, 100), "evaluation date (UTC)",
                    "success rate (%)")
        for key, cikey, cls, shape in (("active_rate", "active_ci", "emp", "circle"),
                                       ("baseline_rate", "baseline_ci", "base", "square")):
            seg = []
            for p in pts:
                if not p["available"]:
                    plot.line(seg, "ln " + cls)
                    seg = []
                    continue
                seg.append((dnum(p["date"]), p[key] * 100))
            plot.line(seg, "ln " + cls)
            for p in pts:
                fa = fattrs(epoch=g["anchor_epoch"], profile=g["profile_id"],
                            notebook=p["active_sha256"], date=p["date"])
                if not p["available"]:
                    plot.text(dnum(p["date"]), 3, "n/a", "ann", "middle")
                    continue
                if p[cikey]:
                    plot.errbar(dnum(p["date"]), p[cikey][0] * 100, p[cikey][1] * 100,
                                "eb " + cls, fa)
                plot.point(dnum(p["date"]), p[key] * 100, shape, cls,
                           "%s: active %s, baseline %s, n=%s, delta %s, lower bound %s" % (
                               p["date"], pct(p["active_rate"]), pct(p["baseline_rate"]),
                               p["n"], pp(p["delta_pp"]), pp(p["lower_bound_pp"])), fa)
        body.append('<h4>%s anchor epoch <code>%s</code> &middot; profile <code>%s</code> '
                    '(model %s, digest %s) &middot; distribution %s</h4>' % (
                        "Epoch boundary &mdash;" if i else "",
                        esc(g["anchor_epoch"]), esc(g["profile_id"]), esc(g["model"]),
                        code(g["profile_digest"]), code(g["mixture_digest"])))
        body.append(plot.render())
        rows = []
        for p in pts:
            rows.append((fattrs(epoch=g["anchor_epoch"], profile=g["profile_id"],
                                notebook=p["active_sha256"], date=p["date"]),
                         [esc(p["date"]), code(p["active_sha256"]), code(p["baseline_sha256"]),
                          fmt(p["n"]), esc(pct(p["active_rate"])),
                          esc(pct(p["baseline_rate"])), esc(pp(p["delta_pp"])),
                          esc(pp(p["lower_bound_pp"])), esc(p["verdict"]),
                          esc(p["baseline_identified_by"])], p["record_ids"]))
        body.append(table("Anchor points, epoch %s" % g["anchor_epoch"],
                          ["Date", "Active notebook", "Baseline", "n", "Active rate",
                           "Baseline rate", "Paired delta", "Lower bound", "Verdict",
                           "Baseline arm"], rows))
    if an["excluded"]:
        body.append(excluded_html(an["excluded"]))
    return section(role + "-anchor", "Anchor learning curve", caption, "".join(body))


def excluded_html(items):
    lis = "".join("<li>%s: %s</li>" % (esc(e["reason"]) + (
        " (%s arm)" % esc(e["arm"]) if e.get("arm") else ""),
        ", ".join(code(r) for r in e["record_ids"])) for e in items)
    return '<p class="warn">Excluded (not comparable or incomplete):</p><ul>%s</ul>' % lis


def render_pareto(role, d):
    pa = d["pareto"]
    caption = ("Note tokens against empirical success rate, one panel per evaluation contract "
               "profile, distribution (mixture), epoch and scope; points from different panels "
               "are never ranked together. The line joins the empirical Pareto frontier of "
               "eligible points (incumbents and passed candidates); bars are Wilson 95% "
               "intervals from recorded counts.")
    if not pa["groups"]:
        body = '<p class="empty">No observations: no comparable comparisons with tokens.</p>'
        if pa["excluded"]:
            body += excluded_html(pa["excluded"])
        return section(role + "-pareto", "Notebook Pareto view", caption, body)
    body = [legend_html([("old hollow", "square", "incumbent"),
                         ("emp", "circle", "candidate: passed (normal)"),
                         ("prov hollow", "diamond", "candidate: provisional"),
                         ("rej", "cross", "candidate: rejected"),
                         ("inc", "triangle", "candidate: inconclusive"),
                         ("front", "line", "empirical Pareto frontier (eligible points)")])]
    for i, g in enumerate(pa["groups"]):
        pts = g["points"]
        xs = [p["tokens"] for p in pts]
        if not pts:
            body.append('<h4>%s &middot; epoch <code>%s</code> &middot; scope <code>%s</code>'
                        '</h4><p class="empty">No plottable points in this group.</p>' % (
                            esc(g["group_id"]), esc(g["epoch_id"]), esc(g["scope"])))
            if g["excluded"]:
                body.append(excluded_html(g["excluded"]))
            continue
        if xs:
            span = max(xs) - min(xs)
            pad = max(1.0, span * 0.08)
            dom = (max(0.0, min(xs) - pad), max(xs) + pad)
        else:
            dom = (0, 1)
        plot = Plot("%s-pareto-%d" % (role, i), "Pareto: %s" % g["group_id"],
                    "Note tokens versus success rate within one comparable group.", dom,
                    (0, 100), "notebook tokens", "success rate (%)", x_kind="linear")
        front = sorted([p for p in pts if p["on_frontier"]], key=lambda p: p["tokens"])
        plot.line([(p["tokens"], p["rate"] * 100) for p in front], "ln front")
        for p in pts:
            cls, shape = ("old hollow", "square") if p["class"] == "incumbent" \
                else CLASS_STYLE[p["class"]]
            fa = fattrs(scope=g["scope"], epoch=g["epoch_id"], profile=g["profile_id"],
                        notebook=p["notebook_sha256"], date=p["date"])
            if p["ci"]:
                plot.errbar(p["tokens"], p["ci"][0] * 100, p["ci"][1] * 100,
                            "eb " + cls.split()[0], fa)
            plot.point(p["tokens"], p["rate"] * 100, shape, cls,
                       "%s %s: %d tokens, %s (n=%d), %s %s" % (
                           p["arm"], short(p["notebook_sha256"]), p["tokens"], pct(p["rate"]),
                           p["n"], p["stage"], p["verdict"]), fa)
        body.append('<h4>%s &middot; epoch <code>%s</code> &middot; scope <code>%s</code> '
                    '&middot; profile <code>%s</code> (%s) &middot; distribution %s</h4>' % (
                        esc(g["group_id"]), esc(g["epoch_id"]), esc(g["scope"]),
                        esc(g["profile_id"]), code(g["profile_digest"]),
                        code(g["mixture_digest"])))
        body.append(plot.render())
        rows = []
        for p in pts:
            rows.append((fattrs(scope=g["scope"], epoch=g["epoch_id"], profile=g["profile_id"],
                                notebook=p["notebook_sha256"], date=p["date"]),
                         [esc(p["date"]), esc(p["arm"]), code(p["notebook_sha256"]),
                          fmt(p["tokens"]), fmt(p["bytes"]), esc(pct(p["rate"])), fmt(p["n"]),
                          esc("%s / %s" % (p["stage"], p["verdict"])), esc(p["class"]),
                          "yes" if p["on_frontier"] else "no"], p["record_ids"]))
        body.append(table("Pareto points, %s" % g["group_id"],
                          ["Date", "Arm", "Notebook", "Tokens", "Bytes", "Success rate", "n",
                           "Stage / verdict", "Class", "On frontier"], rows))
        if g["excluded"]:
            body.append(excluded_html(g["excluded"]))
    if pa["excluded"]:
        body.append(excluded_html(pa["excluded"]))
    return section(role + "-pareto", "Notebook Pareto view", caption, "".join(body))




def tile(label, value, sub=""):
    return ('<div class="tile"><div class="tl">%s</div><div class="tv">%s</div>'
            '<div class="ts">%s</div></div>' % (esc(label), value, sub))


def render_summary_tiles(role, s):
    an = s["active_notebook"]
    lp = s["last_comparable_paired_result"]
    la = s["last_anchor_result"]
    ev = s["evaluations_by_verdict"]
    tiles = [
        tile("Certified generators", esc(s["current_certified_generators"]),
             esc("%d versions, %d families (ever: %d / %d / %d)" % (
                 s["current_certified_versions"], s["current_certified_families"],
                 s["ever_certified_generators"], s["ever_certified_versions"],
                 s["ever_certified_families"]))),
        tile("Quarantined / superseded / rejected",
             esc("%d / %d / %d" % (s["current_quarantined_versions"],
                                   s["current_superseded_versions"], s["rejected_versions"])),
             esc("eligible versions: %d; verified DAG nodes sourced: %d" % (
                 s["eligible_versions"], s["verified_source_nodes"]))),
        tile("Active notebook", code(an["sha256"]) if an else '<span class="muted">none</span>',
             esc("#%s %s%s, %s bytes, %s" % (
                 an["sequence"], an["reason"], " (provisional)" if an["provisional"] else "",
                 an["bytes"] if an["bytes"] is not None else "n/a",
                 ("%d tokens" % an["tokens"]) if an["tokens"] is not None
                 else an["tokens_unavailable_reason"])) if an else ""),
        tile("Last paired comparison", esc(pp(lp["delta_pp"])) if lp else
             '<span class="muted">none</span>',
             esc("%s, %s, LB %s, n=%s, %s" % (lp["date"], lp["verdict"],
                                               pp(lp["lower_bound_pp"]), lp["n"], lp["scope"]))
             if lp else ""),
        tile("Last anchor result", esc(pp(la["delta_pp"])) if la else
             '<span class="muted">none</span>',
             esc("%s, epoch %s, active %s vs baseline %s, n=%s" % (
                 la["date"], la["anchor_epoch"], pct(la["active_rate"]),
                 pct(la["baseline_rate"]), la["n"])) if la else ""),
        tile("Evaluations pending / failed", esc("%d / %d" % (s["evaluations_pending"],
                                                              s["evaluations_failed"])),
             esc("inconclusive %d, stale %d, infra error %d, passed %d" % (
                 ev["inconclusive"], ev["stale"], ev["infra_error"],
                 ev["pass_performance"] + ev["pass_compression"]))),
    ]
    return '<div class="tiles">%s</div>' % "".join(tiles)


def filter_bar(role, html_body):
    values = {dim: set() for dim in FILTER_DIMS}
    for dim in FILTER_DIMS:
        for m in re.finditer(r'data-f-%s="([^"]*)"' % dim, html_body):
            values[dim].add(html.unescape(m.group(1)))
    parts = ['<form class="filters" data-role="%s" hidden aria-label="Filters for %s">' % (
        esc(role), esc(role))]
    for dim in ("family", "profile", "epoch", "scope"):
        opts = "".join('<option value="%s">%s</option>' % (esc(v), esc(v))
                       for v in sorted(values[dim]))
        parts.append('<label>%s <select data-dim="%s"><option value="">all</option>%s'
                     '</select></label>' % (dim, dim, opts))
    parts.append('<label>generator <input type="search" data-dim="generator" '
                 'data-match="substr" placeholder="id or version"></label>')
    parts.append('<label>notebook <input type="search" data-dim="notebook" data-match="substr" '
                 'placeholder="hash prefix"></label>')
    parts.append('<label>from <input type="date" data-dim="date" data-match="from"></label>')
    parts.append('<label>to <input type="date" data-dim="date" data-match="to"></label>')
    parts.append('<button type="reset">Reset</button></form>')
    return "".join(parts)


CSS = """
:root{color-scheme:light;--bg:#ffffff;--panel:#f6f6f4;--text:#191919;--muted:#666666;
--grid:#e4e4e0;--axis:#9c9c9c;--cert:#257de0;--emp:#f47230;--prov:#00a383;--rej:#8a8a8a;
--inc:#b07800;--base:#6a4ce2;--req:#ec4647;--k0:#191919;--warnbg:#fff4e0;--border:#d8d8d4;
--k1:#257de0;--k2:#f47230;--k3:#00b894;--k4:#f2a600;--k5:#ee7fac;--k6:#008a17;--k7:#6a4ce2;
--k8:#ec4647;--band:rgba(0,138,23,.10)}
@media (prefers-color-scheme:dark){:root:not([data-theme="light"]){color-scheme:dark;
--bg:#191919;--panel:#232321;--text:#efefef;--muted:#9c9c9c;--grid:#33332f;--axis:#6c6c6c;
--cert:#338ced;--emp:#e76624;--prov:#00a888;--rej:#9a9a9a;--inc:#d28e05;--base:#9887ef;
--req:#eb6263;--k0:#efefef;--warnbg:#3a2e14;--border:#3a3a36;--k1:#338ced;--k2:#e76624;
--k3:#00a888;--k4:#d28e05;--k5:#e24d8b;--k6:#0aac23;--k7:#9887ef;--k8:#eb6263;
--band:rgba(10,172,35,.14)}}
:root[data-theme="dark"]{color-scheme:dark;--bg:#191919;--panel:#232321;--text:#efefef;
--muted:#9c9c9c;--grid:#33332f;--axis:#6c6c6c;--cert:#338ced;--emp:#e76624;--prov:#00a888;
--rej:#9a9a9a;--inc:#d28e05;--base:#9887ef;--req:#eb6263;--k0:#efefef;--warnbg:#3a2e14;
--border:#3a3a36;--k1:#338ced;--k2:#e76624;--k3:#00a888;--k4:#d28e05;--k5:#e24d8b;
--k6:#0aac23;--k7:#9887ef;--k8:#eb6263;--band:rgba(10,172,35,.14)}
*{box-sizing:border-box}
body{margin:0;background:var(--bg);color:var(--text);font:15px/1.5 system-ui,-apple-system,
"Segoe UI",sans-serif}
main,header{max-width:1100px;margin:0 auto;padding:0 16px}
header{padding-top:20px}
h1{font-size:1.6em;margin:.2em 0}h2{margin-top:1.6em;border-bottom:1px solid var(--border)}
h3{margin:1.2em 0 .2em}h4{font-weight:600;margin:1em 0 .3em;font-size:.95em}
code{font:12px/1.3 ui-monospace,SFMono-Regular,Menlo,monospace;overflow-wrap:anywhere}
.muted{color:var(--muted)}.unavail{color:var(--muted);font-style:italic}
.caption{color:var(--muted);margin:.2em 0 .6em;max-width:80ch}
.note{background:var(--panel);border:1px solid var(--border);border-radius:8px;padding:10px 14px}
.warn{background:var(--warnbg);border-radius:6px;padding:6px 10px}
.empty{background:var(--panel);border-radius:6px;padding:10px 14px;color:var(--muted)}
nav.roles{display:flex;gap:8px;margin:12px 0}
nav.roles a{padding:6px 14px;border:1px solid var(--border);border-radius:999px;color:var(--text);
text-decoration:none}nav.roles a[aria-current="true"]{background:var(--text);color:var(--bg)}
.tiles{display:grid;grid-template-columns:repeat(auto-fit,minmax(200px,1fr));gap:10px;margin:10px 0}
.tile{background:var(--panel);border-radius:8px;padding:10px 12px}
.tl{font-size:.8em;color:var(--muted)}.tv{font-size:1.4em;font-weight:600}
.ts{font-size:.8em;color:var(--muted);overflow-wrap:anywhere}
.chartsec{margin:24px 0 32px}
svg.chart{width:100%;height:auto;max-width:900px;display:block;background:var(--bg)}
.grid{stroke:var(--grid);stroke-width:1}.axis{stroke:var(--axis);stroke-width:1}
.tick,.ann,.axlabel{fill:var(--muted);font-size:11px}.axlabel{font-size:12px}
.ln{fill:none;stroke-width:2}.dash,.ln.dash{stroke-dasharray:5 4}
.pt{stroke:var(--bg);stroke-width:2}.pt .hit{fill:transparent;stroke:none}
.pt:focus{outline:none}.pt:focus circle:not(.hit),.pt:hover circle:not(.hit){stroke:var(--text)}
.xmark{fill:none!important;stroke-width:2.5}
.eb{fill:none;stroke-width:1.5}
.band{fill:var(--band);stroke:none}.bandsw{fill:var(--band)}
.tgt{stroke:var(--k6);stroke-width:1.5}.zero{stroke:var(--axis);stroke-width:1}
.cap{stroke:var(--req);stroke-width:1.5}
.act{stroke:var(--muted);stroke-width:1;stroke-dasharray:2 3}
.boundary{stroke:var(--text);stroke-width:1.5;stroke-dasharray:6 3}
.legend{list-style:none;display:flex;flex-wrap:wrap;gap:4px 16px;padding:0;margin:6px 0;
font-size:.85em}.legend li{display:flex;align-items:center;gap:6px}
.legend line{stroke:var(--text);stroke-width:2}.legend .tgt line{stroke:var(--k6)}
.legend .cap line{stroke:var(--req)}.legend .front line{stroke:var(--cert)}
""" + "".join(
    ".%s{fill:var(--%s);color:var(--%s)}.%s .xmark,.ln.%s,.eb.%s{stroke:var(--%s)}\n" % (
        c, v, v, c, c, c, v) for c, v in (
        ("cert", "cert"), ("emp", "emp"), ("prov", "prov"), ("rej", "rej"), ("inc", "inc"),
        ("base", "base"), ("req", "req"), ("k0", "k0"), ("old", "muted"), ("k1", "k1"),
        ("k2", "k2"), ("k3", "k3"), ("k4", "k4"), ("k5", "k5"), ("k6", "k6"), ("k7", "k7"),
        ("k8", "k8"), ("g0", "k3"), ("g1", "k1"), ("g2", "k7"), ("g3", "k5"), ("g4", "rej"),
        ("front", "cert"))) + """
.pt.hollow>*:not(.hit){fill:var(--bg);stroke:currentColor;stroke-width:2}
.pt.sel>circle:not(.hit){stroke:var(--text);stroke-width:2.5}
path.ln,path.eb{fill:none!important}
.bar{stroke:var(--bg);stroke-width:1.5}
.bar.hollowbar{fill:var(--bg);stroke:var(--prov);stroke-width:2;stroke-dasharray:4 2}
.ln.req{stroke:var(--req)}
.tablewrap{overflow-x:auto;margin:8px 0;max-width:100%}
table{border-collapse:collapse;font-size:.82em;min-width:60%}
caption{text-align:left;font-weight:600;padding:4px 0}
th,td{border-bottom:1px solid var(--border);padding:3px 8px;text-align:left;vertical-align:top}
th{background:var(--panel);position:sticky;top:0}
.filters{display:flex;flex-wrap:wrap;gap:6px 12px;align-items:center;background:var(--panel);
padding:8px 12px;border-radius:8px;font-size:.85em}
.filters select,.filters input,.filters button{font:inherit;color:var(--text);background:var(--bg);
border:1px solid var(--border);border-radius:4px;padding:2px 4px;max-width:180px}
.f-off{display:none}
dl.legendkey{display:grid;grid-template-columns:max-content 1fr;gap:4px 12px;margin:0}
dl.legendkey dt{font-weight:600}dl.legendkey dd{margin:0}
@media (max-width:600px){body{font-size:14px}.tv{font-size:1.2em}}
"""

JS = r"""
(function(){
  var secs=document.querySelectorAll('section.role');
  var tabs=document.querySelectorAll('nav.roles a');
  function show(id){
    for(var i=0;i<secs.length;i++){secs[i].hidden=(secs[i].id!==id);}
    for(var j=0;j<tabs.length;j++){tabs[j].setAttribute('aria-current',
      tabs[j].getAttribute('href')==='#'+id?'true':'false');}
  }
  for(var t=0;t<tabs.length;t++){tabs[t].addEventListener('click',function(e){
    e.preventDefault();var id=this.getAttribute('href').slice(1);show(id);
    try{history.replaceState(null,'','#'+id);}catch(err){}});}
  var start=(location.hash||'').slice(1);
  show(document.getElementById(start)&&start.indexOf('role-')===0?start:
       (secs.length?secs[0].id:''));
  var forms=document.querySelectorAll('form.filters');
  for(var f=0;f<forms.length;f++){(function(form){
    form.hidden=false;
    var root=document.getElementById('role-'+form.getAttribute('data-role'));
    function apply(){
      var ctl=form.querySelectorAll('[data-dim]');var items=root.querySelectorAll(
        '[data-f-family],[data-f-generator],[data-f-profile],[data-f-epoch],[data-f-scope],'+
        '[data-f-notebook],[data-f-date]');
      for(var i=0;i<items.length;i++){
        var el=items[i],ok=true;
        for(var c=0;c<ctl.length&&ok;c++){
          var dim=ctl[c].getAttribute('data-dim'),mode=ctl[c].getAttribute('data-match')||'eq',
              want=ctl[c].value,have=el.getAttribute('data-f-'+dim);
          if(!want||have===null){continue;}
          if(mode==='eq'){ok=(have===want);}
          else if(mode==='substr'){ok=have.toLowerCase().indexOf(want.toLowerCase())>=0;}
          else if(mode==='from'){ok=have>=want;}else if(mode==='to'){ok=have<=want;}
        }
        if(ok){el.classList.remove('f-off');}else{el.classList.add('f-off');}
      }
    }
    form.addEventListener('input',apply);form.addEventListener('change',apply);
    form.addEventListener('reset',function(){setTimeout(apply,0);});
  })(forms[f]);}
})();
"""


def render_issues(data):
    issues = data["issues"]
    if not issues:
        return '<p>No malformed or inconsistent records were found.</p>'
    rows = []
    for i in issues:
        rows.append(("", [esc(i["file"]), fmt(i["line"]), esc(i["problem"]), esc(i["action"])],
                     [i["record_id"]] if i["record_id"] else []))
    return table("Record issues", ["File", "Line", "Problem", "Action"], rows)


def render_html(data):
    if data["as_of"]:
        stamp = "Records as of %s (end of day, UTC); the generated-at timestamp is omitted for " \
                "reproducibility." % esc(data["as_of"])
    else:
        stamp = "Generated at %s (the only non-deterministic field; use --as-of to omit it)." % (
            esc(data["generated_at"]))
    inputs = ", ".join("%s: %d loaded%s" % (esc(k), v["loaded"],
                                            "" if v["present"] else " (file absent)")
                       for k, v in sorted(data["inputs"].items()))
    pol = data["policy"]
    parts = ['<!doctype html><html lang="en"><head><meta charset="utf-8">'
             '<meta name="viewport" content="width=device-width,initial-scale=1">'
             '<title>Learning Progress Report</title><style>%s</style></head><body>' % CSS]
    parts.append('<header><h1>Learning progress report</h1><p class="muted">%s</p>'
                 '<nav class="roles" aria-label="Roles">%s</nav></header><main>' % (
                     stamp, "".join('<a href="#role-%s">%s</a>' % (r, ROLE_TITLES[r])
                                    for r in ROLES)))
    parts.append(
        '<div class="note"><p><b>%s</b></p><dl class="legendkey">'
        '<dt><span class="cert">&#9632;</span> Certified</dt><dd>Formally checked by Lean in the '
        'certification record (seed bits, the certified entropy lower bound, admission status). '
        'Not a statement about difficulty or performance.</dd>'
        '<dt><span class="emp">&#9679;</span> Empirical</dt><dd>Estimated from model trials under '
        'a stated profile (success rates, paired differences, intervals). Intervals assume '
        'independent sampling; provider drift and correlated tasks may weaken them.</dd>'
        '<dt><span class="prov">&#9670;</span> Provisional</dt><dd>Fresh-seed (within-family) '
        'evidence accepted under the maintainer bootstrap rule; not general research '
        'improvement.</dd></dl><p class="muted">Units: rates in percent, differences in '
        'percentage points (pp), entropy and seeds in bits, notebook size in tokens and bytes, '
        'counts of trials. Missing data is shown as n/a, never as zero; lines are never '
        'interpolated across gaps or contract/profile changes. Curriculum thresholds: %s. '
        'Inputs: %s.</p></div>' % (
            esc(ADVERSARY_STATEMENT), esc(data["roles"]["design"]["difficulty"]["source"]),
            inputs))
    for role in ROLES:
        d = data["roles"][role]
        sec = [render_library(role, d), render_diversity(role, d), render_difficulty(role, d),
               render_allocation(role, d), render_performance(role, d),
               render_compression(role, d), render_anchors(role, d), render_pareto(role, d)]
        body = "".join(sec)
        parts.append('<section class="role" id="role-%s"><h2>%s</h2>%s%s%s</section>' % (
            role, ROLE_TITLES[role], render_summary_tiles(role, d["summary"]),
            filter_bar(role, body), body))
    parts.append('<h2>Record integrity</h2>%s' % render_issues(data))
    parts.append('<p class="muted">Derived data: <code>data.json</code>; tables: '
                 '<code>generators.csv</code>, <code>calibrations.csv</code>, '
                 '<code>comparisons.csv</code>, <code>activations.csv</code>, '
                 '<code>anchors.csv</code>; summary: <code>LEARNING.md</code>. Policy: %s.</p>'
                 % esc(pol["policy_id"] or "none supplied"))
    parts.append('<script type="application/json" id="report-data">%s</script>'
                 % json_for_script(data))
    parts.append("<script>%s</script></main></body></html>\n" % JS)
    return "".join(parts)


# ---------------------------------------------------------------------------------------------
# LEARNING.md and CSV
# ---------------------------------------------------------------------------------------------

def render_markdown(data):
    lines = ["# Learning progress summary", ""]
    if data["as_of"]:
        lines.append("Records as of %s (UTC, end of day)." % md(data["as_of"]))
    else:
        lines.append("Generated at %s." % md(data["generated_at"]))
    lines += ["", "**%s**" % md(ADVERSARY_STATEMENT), "",
              "Certified entropy figures are Lean-checked lower bounds; success rates are "
              "empirical estimates for the stated profile (difficulty = 1 \u2212 p). See "
              "`index.html` for charts and `data.json` / CSV files for the records behind each "
              "number.", ""]
    for role in ROLES:
        s = data["roles"][role]["summary"]
        lines.append("## %s" % ROLE_TITLES[role])
        lines.append("")
        lines.append("- Certified generators (current): %d unique generators, %d unique "
                     "families, %d versions." % (s["current_certified_generators"],
                                                 s["current_certified_families"],
                                                 s["current_certified_versions"]))
        lines.append("- Ever certified: %d generators, %d families, %d versions; quarantined "
                     "%d, superseded %d, rejected %d; eligible %d." % (
                         s["ever_certified_generators"], s["ever_certified_families"],
                         s["ever_certified_versions"], s["current_quarantined_versions"],
                         s["current_superseded_versions"], s["rejected_versions"],
                         s["eligible_versions"]))
        lines.append("- Verified DAG nodes sourced by certified generators: %d." %
                     s["verified_source_nodes"])
        an = s["active_notebook"]
        if an:
            lines.append("- Active notebook: %s (activation %s, %s%s, %s): %s bytes, %s." % (
                md_id(an["sha256"]), md(an["sequence"]), md(an["reason"]),
                md(" provisional" if an["provisional"] else ""), md(an["date"]),
                md(an["bytes"] if an["bytes"] is not None else "n/a"),
                md("%d tokens (%s)" % (an["tokens"], an["tokenizer"]) if an["tokens"]
                   is not None else "tokens unavailable: %s" % an["tokens_unavailable_reason"])))
        else:
            lines.append("- Active notebook: none (no valid activation).")
        lp = s["last_comparable_paired_result"]
        if lp:
            lines.append("- Last paired comparison: %s, %s %s, n = %s, old %s, new %s, delta %s, "
                         "lower bound %s, verdict %s, scope %s, contract %s." % (
                             md(lp["date"]), md(lp["stage"]), md(lp["reason"]), md(lp["n"]),
                             md(pct(lp["incumbent_rate"])), md(pct(lp["candidate_rate"])),
                             md(pp(lp["delta_pp"])), md(pp(lp["lower_bound_pp"])),
                             md(lp["verdict"]),
                             md(lp["scope"] + (" provisional" if lp["provisional"] else "")
                                if lp["scope"] else None), md_id(lp["contract_id"])))
        else:
            lines.append("- Last paired comparison: none with completed pairs.")
        la = s["last_anchor_result"]
        if la:
            lines.append("- Last anchor result: %s, anchor epoch %s, profile %s, active %s vs "
                         "baseline %s, n = %s, paired delta %s." % (
                             md(la["date"]), md(la["anchor_epoch"]), md(la["profile_id"]),
                             md(pct(la["active_rate"])), md(pct(la["baseline_rate"])),
                             md(la["n"]), md(pp(la["delta_pp"]))))
        else:
            lines.append("- Last anchor result: none.")
        ev = s["evaluations_by_verdict"]
        lines.append("- Evaluations: %d pending (awaiting evaluator), %d failed (%d fail, %d "
                     "infra error), %d inconclusive, %d stale, %d passed." % (
                         s["evaluations_pending"], s["evaluations_failed"], ev["fail"],
                         ev["infra_error"], ev["inconclusive"], ev["stale"],
                         ev["pass_performance"] + ev["pass_compression"]))
        u = s["usage"]
        lines.append("- Recorded trial usage: %d trials, %s model calls, %s input tokens, %s "
                     "output tokens (fields unavailable in %s trials are not counted)." % (
                         u["trials"], md(u["totals"]["model_calls"]),
                         md(u["totals"]["input_tokens"]), md(u["totals"]["output_tokens"]),
                         md(max(u["unavailable_counts"][f] for f in
                                ("model_calls", "input_tokens", "output_tokens")))))
        lines.append("")
    lines.append("## Record integrity")
    lines.append("")
    if data["issues"]:
        lines.append("%d record issue(s); see the report's integrity table:" %
                     len(data["issues"]))
        for i in data["issues"]:
            lines.append("- %s line %s: %s (%s)" % (md(i["file"]), md(i["line"] or "n/a"),
                                                    md(i["problem"]), md(i["action"])))
    else:
        lines.append("No malformed or inconsistent records.")
    lines.append("")
    return "\n".join(lines)


def write_csv(path, headers, rows):
    buf = io.StringIO()
    w = csv.writer(buf, lineterminator="\n")
    w.writerow(headers)
    for r in rows:
        w.writerow([csv_cell(r.get(h)) if h != "record_ids" else " ".join(r.get(h) or [])
                    for h in headers])
    with open(path, "w", encoding="utf-8", newline="") as fh:
        fh.write(buf.getvalue())


def write_csvs(out_dir, data):
    gens, cals, cmps, acts, anchors = [], [], [], [], []
    for role in ROLES:
        d = data["roles"][role]
        for r in d["generators"]["rows"]:
            gens.append(dict(r, role=role))
        for panel in d["difficulty"]["panels"]:
            for p in panel["points"]:
                cals.append(dict(p, role=role, family_id=panel["family_id"],
                                 generator_id=panel["generator_id"], version=panel["version"],
                                 profile_id=panel["profile_id"],
                                 reference_notebook_sha256=panel["reference_notebook_sha256"],
                                 failures=p["failures"], notes="; ".join(p["notes"])))
        for p in d["performance"]["points"]:
            if p["kind"] == "comparison":
                cmps.append(dict(p, role=role, notes="; ".join(p["notes"])))
        for r in d["compression"]["rows"]:
            acts.append(dict(r, role=role, comparison_ids=" ".join(r["comparison_ids"])))
        for g in d["anchors"]["series"]:
            for p in g["points"]:
                anchors.append(dict(p, role=role, series_id=g["series_id"],
                                    anchor_epoch=g["anchor_epoch"], profile_id=g["profile_id"],
                                    model=g["model"], profile_digest=g["profile_digest"],
                                    mixture_digest=g["mixture_digest"],
                                    notes="; ".join(p["notes"])))
    write_csv(os.path.join(out_dir, "generators.csv"), [
        "role", "family_id", "generator_id", "version", "status", "reason", "seed_bits",
        "entropy_bits", "required_bits", "levels", "equivalence", "bootstrap", "eligible",
        "first_certified_at", "latest_at", "pr", "head", "author", "record_ids"], gens)
    write_csv(os.path.join(out_dir, "calibrations.csv"), [
        "role", "family_id", "generator_id", "version", "level", "profile_id",
        "reference_notebook_sha256", "created_at", "n", "successes", "infra_errors", "failures",
        "p_hat", "ci_method", "ci_low", "ci_high", "state", "selected", "eligibility",
        "contract_id", "notes", "record_ids"], cals)
    write_csv(os.path.join(out_dir, "comparisons.csv"), [
        "role", "order", "created_at", "contract_id", "stage", "scope", "provisional", "verdict",
        "reason", "n", "incumbent_sha256", "candidate_sha256", "incumbent_successes",
        "candidate_successes", "incumbent_rate", "candidate_rate", "w", "l", "both_solved",
        "both_failed", "delta_hat", "delta_pp", "lower_bound", "lower_bound_pp", "method",
        "alpha", "delta_ni", "incumbent_bytes", "incumbent_tokens", "candidate_bytes",
        "candidate_tokens", "cap_tokens", "tokenizer", "profile_id", "model", "profile_digest",
        "mixture_digest", "epoch_id", "policy_id", "pr", "head", "notes", "record_ids"], cmps)
    write_csv(os.path.join(out_dir, "activations.csv"), [
        "role", "sequence", "created_at", "reason", "scope", "provisional", "predecessor_sha256",
        "successor_sha256", "pr", "merge_commit", "actor", "policy_id", "epoch_id", "bytes",
        "tokens", "tokens_unavailable_reason", "tokenizer", "cap_tokens", "cap_bytes",
        "successor_success_rate", "successor_n", "comparison_ids", "record_ids"], acts)
    write_csv(os.path.join(out_dir, "anchors.csv"), [
        "role", "series_id", "anchor_epoch", "profile_id", "model", "profile_digest",
        "mixture_digest", "created_at", "contract_id", "n", "active_sha256", "baseline_sha256",
        "active_successes", "baseline_successes", "active_rate", "baseline_rate", "active_ci",
        "baseline_ci", "delta_pp", "lower_bound_pp", "verdict", "baseline_identified_by",
        "notes", "record_ids"], anchors)


# ---------------------------------------------------------------------------------------------
# Entry points
# ---------------------------------------------------------------------------------------------

def parse_as_of(value):
    if value is None or isinstance(value, datetime.date):
        return value
    try:
        return datetime.datetime.strptime(value, "%Y-%m-%d").date()
    except ValueError:
        raise ValueError("--as-of must be YYYY-MM-DD, got %r" % value)


def build_report(records_dir, out_dir, as_of=None, policy=None):
    """Build the report from ``records_dir`` into ``out_dir``; returns the derived data."""
    as_of = parse_as_of(as_of)
    pview = policy_view(load_policy(policy))
    records, issues, inputs = load_records(records_dir, as_of)
    generated_at = None
    if as_of is None:
        generated_at = datetime.datetime.now(datetime.timezone.utc).strftime(
            "%Y-%m-%dT%H:%M:%SZ")
    data = derive(records, issues, inputs, pview, as_of, generated_at)
    os.makedirs(out_dir, exist_ok=True)
    with open(os.path.join(out_dir, "data.json"), "w", encoding="utf-8") as fh:
        fh.write(json.dumps(data, sort_keys=True, indent=1, ensure_ascii=True,
                            allow_nan=False) + "\n")
    with open(os.path.join(out_dir, "index.html"), "w", encoding="utf-8") as fh:
        fh.write(render_html(data))
    with open(os.path.join(out_dir, "LEARNING.md"), "w", encoding="utf-8") as fh:
        fh.write(render_markdown(data))
    write_csvs(out_dir, data)
    return data


def main(argv=None):
    parser = argparse.ArgumentParser(
        prog="python3 -m ci.learning.report",
        description="Generate the learning progress report (HTML, Markdown, JSON, CSV) from "
                    "the learning records. Makes no model or network calls.")
    parser.add_argument("--records", required=True, help="directory with the *.jsonl records")
    parser.add_argument("--out", required=True, help="output directory")
    parser.add_argument("--as-of", help="YYYY-MM-DD: ignore records created after this day and "
                                        "omit the generated-at timestamp")
    parser.add_argument("--policy", help="policy file (meta/learning.json)")
    args = parser.parse_args(argv)
    try:
        data = build_report(args.records, args.out, as_of=args.as_of, policy=args.policy)
    except (OSError, ValueError) as exc:
        print(json.dumps({"ok": False, "error": str(exc)}), file=sys.stderr)
        return 2
    print(json.dumps({"ok": True, "out": args.out, "issues": len(data["issues"]),
                      "as_of": data["as_of"]}, sort_keys=True))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
