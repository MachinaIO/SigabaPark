# Learning records (contract v1)

The records of the certified curriculum and notebook learning extension (core specification
"SigabaNeo: Certified Curriculum and Collective Research Learning", section 10.2). Every record is
one JSON object; the JSON Schemas in `ci/learning/schemas/` are the authority and this file
describes them. All records are produced by the trusted CI code in `ci/learning/` (or by a
maintainer's authorized evaluator run of that same code), never taken from pull request text.

## Conventions

- Canonical JSON: UTF-8, object keys sorted, separators `,` and `:` (no whitespace), integers only
  where a count is meant, no NaN/Infinity. Floats are allowed only in derived statistics fields
  (`p_hat`, `ci_low`, ...) and are written with Python's `repr` of a finite float.
- Digests are `sha256:<64 hex>` of the canonical JSON or of the exact bytes named.
- `record_id` = `sha256:` of the canonical JSON of the record **without** `record_id`,
  `created_at` and `generated_at`.
- Timestamps: ISO 8601 UTC with `Z` (`2026-11-28T12:00:00Z`).
- Git revisions: full 40-hex SHAs. Lean names: fully qualified.
- `role` is `design` or `cryptanalysis`. `adversary_model` is always `classical`.
- Common fields of every stored record: `schema`, `record_id`, `created_at`, `core_revision`,
  `dag_snapshot` (DAG commit), `environment_id` (from `env/environments.json`).

## Storage

Branch `learning-records` (protected; only the `learning` workflow's trusted jobs and maintainers
write it), one JSONL file per kind, append-only:

```
certifications.jsonl   sigaba.learning.certification.v1
calibrations.jsonl     sigaba.learning.calibration.v1
contracts.jsonl        sigaba.learning.contract.v1
trials.jsonl           sigaba.learning.trial.v1
comparisons.jsonl      sigaba.learning.comparison.v1
activations.jsonl      sigaba.learning.activation.v1
reveals.jsonl          sigaba.learning.reveal.v1      (seeds and descriptors after a comparison ends)
```

The generated report goes to the branch `learning-report` (never `main`).

## Contributor files on `main`

- `generators/<role>/<family_id>/<generator_id>/v<NNNN>/manifest.json` (`sigaba.generator.v1`),
  `Generate.lean`, `Certificate.lean`. Identifiers match `[a-z0-9][a-z0-9-]{0,62}`; versions are
  4 digits starting at `v0001`; versions are immutable (added only).
- `notebooks/design.md`, `notebooks/cryptanalysis.md`: the role notebooks (UTF-8 Markdown).
- `meta/learning.json` (`sigaba.learning.policy.v1`): maintainers only.

### `sigaba.generator.v1` (manifest, contributor-supplied, validated)

`schema`, `role`, `family_id`, `family_revision` (`sha256:` of the family adapter source as
pinned by policy), `generator_id`, `version` (int >= 1, equal to the directory's), `parent`
(`null` or `{"generator_id", "version"}`), `seed_bits` (int), `levels` (int, number of levels
L, 1..policy max), `generate_decl`, `certificate_decl` (Lean names; the certificate's type must be
`SigabaNeo.Benchmark.Certified <family> L k h <generate>`), `source_refs` (non-empty list of
`{"node_id": "theorem:..|definition:..|solution:..", "commit": 40-hex, "content_sha256":
"sha256:.."}`; bootstrap generators instead set `bootstrap: {"approved_by": login, "provenance":
text}` which only a maintainer-approved policy entry can accept), `description` (<= 2000 chars).
The required entropy `h` is **not** in the manifest: it comes from the family's policy entry.

### `sigaba.learning.policy.v1` (`meta/learning.json`)

```json
{
  "schema": "sigaba.learning.policy.v1",
  "policy_id": "policy-0001",
  "epoch": {"id": "epoch-0001", "dag_snapshot": "<40hex>", "environment_id": "env-3",
            "core_revision": "<40hex>", "strength_digest": "sha256:..."},
  "families": [{"family_id": "avoid-word", "role": "design",
                "lean_module": "SigabaNeoStd.Benchmarks.Families.AvoidWord",
                "lean_family": "SigabaNeo.Benchmark.Families.AvoidWord.family",
                "revision": "sha256:...", "group": "bootstrap-avoid",
                "seed_bits": 16, "entropy_bits": 16, "max_levels": 8,
                "max_descriptor_bits": 4096, "assessment": "training",
                "bootstrap": true, "approved_by": "SoraSuegami"}],
  "bootstrap_generators": [{"family_id": "...", "generator_id": "...", "version": 1}],
  "notebooks": {"max_tokens": 4096, "max_bytes": 32768,
                "tokenizer": {"kind": "proxy-bytes-div-3", "version": "1"}},
  "curriculum": {"target": 0.40, "lo": 0.20, "hi": 0.60, "min_samples": 20,
                 "exploration_fraction": 0.10, "stale_after_days": 30},
  "promotion": {"screen_pairs": 20, "confirm_pairs": 100, "alpha": 0.05, "delta_ni": 0.05,
                "infra_retries": 1, "provisional_within_family": false,
                "require_family_disjoint": true},
  "profiles": [{"profile_id": "profile-0001", "role": "design", "provider": "mock",
                "model": "mock-1", "settings": {}, "budget": {"max_model_calls": 50,
                "max_input_tokens": 400000, "max_output_tokens": 100000,
                "wall_seconds": 3600, "lean_seconds": 1800}}],
  "evaluator": {"enabled": false, "provider": null, "max_trials_per_run": 0}
}
```

`evaluator.enabled = false` (the default) means notebook comparisons are `awaiting_evaluator`.
Probabilities in policy are written as decimal strings or numbers; code converts them to
`fractions.Fraction` through `str` before use.

## Records

### `sigaba.learning.certification.v1`
`role`, `family_id`, `family_revision`, `generator_id`, `version`, `path`, `pr`, `head`
(40-hex), `author`, `files` (`{path: "sha256:.."}`), `seed_bits` k, `levels` L, `entropy_bits`
(certified lower bound h, equal to the policy's requirement when it passed), `required_bits`,
`equivalence` (the family's Lean `SameProblem` name), `certificate_decl`, `generate_decl`,
`lean_result` (verdict, problems), `smoke` (`[{level, seed_commitment, descriptor_sha256,
status}]`), `status` (`certified | rejected | quarantined | superseded`), `reason`,
`source_refs`, `bootstrap` (bool).

### `sigaba.learning.contract.v1`
`contract_id` (= `record_id`), `stage` (`calibration | screen | confirm | anchor | transfer`),
`role`, `scope` (`fresh_seed | family_disjoint | future_family`), `provisional` (bool),
`arms`: `[{"arm": "incumbent|candidate|reference|anchor_baseline", "notebook_sha256",
"notebook_bytes", "notebook_tokens" (int or null), "pr": int|null, "head": 40hex|null}]`,
`mixture`: `[{"family_id", "generator_id", "version", "level", "weight": [num, den]}]`,
`excluded_families`, `trials_planned` (int), `profile` (the full profile object), `policy_id`,
`policy_sha256`, `epoch_id`, `calibration_snapshot` (list of calibration record ids),
`rng` (`{"source": "os.urandom", "algorithm": "sigaba-learning-sample-v1"}`),
`seed_commitment_scheme` (`sha256(domain || salt || seed)`), `verifier`
(`{"core_revision", "environment_id"}`), `score_rule` ("binary-v1"), `statistics`
(`{"method": "cp-union-v1", "alpha", "delta_ni"}`).

### `sigaba.learning.trial.v1`
`run_id`, `contract_id`, `stage`, `pair_id` (int index within the contract, or null for
calibration), `arm`, `role`, `family_id`, `generator_id`, `version`, `level`,
`seed_commitment` (`sha256:..`), `descriptor_sha256`, `notebook_sha256`, `model_reported`,
`started_at`, `ended_at`, `outcome` (`solved | unsolved | infra_error`), `reason`
(`verified | invalid_proof | wrong_target | budget_exhausted | solver_timeout | no_answer |
provider_error | generation_error | verification_infra_error | canceled`), `check`
(`{"verdict", "theorem_sha256"}` or null), `usage` (`{"model_calls", "input_tokens",
"output_tokens", "reasoning_tokens", "cached_tokens", "wall_seconds", "lean_seconds"}`, each int or
null when unavailable), `retries` (int), `certified_value` (`{"kind": "N"|"c", "value": int}` or
null).

### `sigaba.learning.calibration.v1`
`role`, `family_id`, `generator_id`, `version`, `level`, `profile_id`, `reference_notebook_sha256`,
`contract_id`, `trial_ids`, `n`, `successes`, `failures` (`{reason: count}`), `infra_errors`,
`p_hat` (null when n = 0), `ci` (`{"method": "wilson-95", "low", "high"}` or null), `usage`,
`state` (`fresh | stale`), `selected` (bool: the level chosen for this generator),
`eligibility` (`eligible | low_priority | uncalibrated`).

### `sigaba.learning.comparison.v1`
`role`, `contract_id`, `stage`, `scope`, `provisional`, `incumbent_sha256`, `candidate_sha256`,
`pr`, `head`, `pair_refs` (list of `[incumbent_trial_id, candidate_trial_id]`), `n`,
`incumbent_successes`, `candidate_successes`, `w`, `l`, `both_solved`, `both_failed`,
`delta_hat` (float or null), `lower_bound` (float or null), `method` ("cp-union-v1"), `alpha`,
`delta_ni`, `notebook` (`{"incumbent_bytes", "incumbent_tokens", "candidate_bytes",
"candidate_tokens", "cap_tokens", "tokenizer"}`), `usage` (`{"incumbent": {...},
"candidate": {...}}`), `verdict` (`pass_performance | pass_compression | fail | inconclusive |
awaiting_evaluator | stale | infra_error`), `reason`, `policy_id`, `epoch_id`, `anchor_epoch`
(string or null; set for stage `anchor`).

### `sigaba.learning.activation.v1`
`role`, `predecessor_sha256`, `successor_sha256`, `pr`, `head`, `merge_commit`,
`comparison_ids`, `scope`, `provisional`, `reason` (`improvement | compression | rollback |
bootstrap`), `actor`, `policy_id`, `epoch_id`, `anchor_refs`, `sequence` (int, 1-based per role;
activations are applied in this order and each must name the current active hash as
predecessor: compare-and-swap).

### `sigaba.learning.reveal.v1`
`contract_id`, `items`: `[{"pair_id", "family_id", "generator_id", "version", "level",
"seed_bits": "<0/1 string>", "salt": "<hex>", "seed_commitment", "descriptor_bits"}]`, published
only after the contract's comparison (or calibration) is complete.
