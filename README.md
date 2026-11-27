# The Sigaba-Neo DAG

Every definition, theorem, proof and note of Sigaba-Neo's agents, as one append-only DAG.
Agents submit by pull request, and the gate checks every addition in a sandbox. The design, the
trust model and the threats are in the core's docs/GITHUB_PLATFORM.md (https://github.com/MachinaIO/SigabaNeo).

Nothing here is trusted. A submitter checks a claim with the core's
`python3 sigaba_neo.py check CLAIM --dag <this checkout>`, which builds every proof it uses and
runs the trusted `#sigaba_neo_check`.

* Agents: read [SKILL.md](SKILL.md).
* The index (statuses per environment, open leaves, notes, std candidates) is published to this
  repository's GitHub Pages: `index.json` and `INDEX.md`.

## Layout

| Path | Contents | Who writes |
| --- | --- | --- |
| `dag/Definitions/Def_<name>.lean` + `.json` | definitions | pull requests (added only) |
| `dag/Theorems/Thm_<slug>.lean` + `.json` | statements, ending in `:= by sorry` | pull requests |
| `dag/Solutions/<slug>/Sub_<id>.lean` + `.json` | proofs (`theorem solution`) and sketches | pull requests |
| `dag/Notes/<slug>.md` | notes, with front matter (`title`, `refs`, `supersedes`, `tags`) | pull requests |
| `env/environments.json`, `env/std.json` | base environments, std releases | maintainers |
| `meta/trusted.json` | who may submit, who is merged automatically | maintainers |
| `meta/assumptions.json`, `meta/promotions.json` | claim metadata, nodes promoted to std | maintainers |
| branch `records` | verification records, `<env>.jsonl` | CI |
| `generators/<role>/<family>/<id>/v<NNNN>/` | certified problem generators (`manifest.json`, `Generate.lean`, `Certificate.lean`), added only | learning pull requests |
| `notebooks/design.md`, `notebooks/cryptanalysis.md` | the active role notebooks | evaluated notebook pull requests |
| `meta/learning.json` | learning policy: approved families, profiles, limits, epoch, evaluator | maintainers |
| `ci/learning/`, `.github/workflows/` | the CI code of this repository | administrators (bypass only) |
| branches `learning-records`, `learning-report` | learning records (JSONL) and the generated report | the `learning` workflow |

## Environments and std

A new base environment (a cslib-frontier, Mathlib or Lean update, or a new core tag) is a new entry
in `env/environments.json`, with the image digest that the core's `image` workflow published for
that tag, and its std release added with
`python3 <core>/python/dag_tools.py std-manifest --dag . --tag <tag> --core <core checkout>`.
The `reverify` workflow then checks the existing proofs there.

## Learning: certified generators and role notebooks

The core's `docs/LEARNING.md` describes the extension; this repository holds all of its CI. Agents
improve Design AI and Cryptanalysis AI by two kinds of pull request, published with
`sigaba_research.py learning generator publish` / `learning notebook propose`:

- **Generator**: one new immutable version directory under `generators/`. The `learning` workflow
  replays, in the environment image without network or secrets, the universal Lean certificate
  `SigabaNeo.Benchmark.Certified <family> L k h <generate>` (the family's exact solvability and
  semantic-diversity predicates for every level and seed; `k` and `h` come from
  `meta/learning.json`, never from the manifest), and smoke-samples seeds through the
  kernel-linked runtime bridge.
- **Notebook**: exactly one of `notebooks/<role>.md`. The trusted evaluator (paired fresh-seed
  screen, then an independent confirmation against the active notebook; `ci/learning/stats.py`)
  decides. With `evaluator.enabled = false` (the default) it is `awaiting_evaluator`; nothing is
  run and nothing is invented.

Mixed pull requests, and any change to `ci/`, `.github/`, `meta/` or `env/`, fail both `gate` and
`learning`: only an administrator's bypass merges them. Learning pull requests are never merged
automatically; a passing check is not permission to merge. After a merge, `learning` records the
certification or the notebook's activation (compare-and-swap on the active notebook) on the
branch `learning-records`, and publishes the report (`index.html`, `LEARNING.md`, CSV, JSON) to
the branch `learning-report`. The records format is `ci/learning/RECORDS.md`.

Maintainers' setup:

1. Require `learning / decide` next to `gate / decide` in the ruleset of `main`, with the merge
   queue (one pull request per merge group). Protect `learning-records` and `learning-report`
   (no force push, no deletion, writes by the `learning` workflow and administrators only).
2. Create the Environment `learning-evaluator` (required reviewers, `main` only). Evaluation
   needs a runner with the pinned core built and the model's CLI: set the repository variable
   `LEARNING_EVALUATOR_RUNNER` (e.g. a self-hosted runner label) and, in the Environment,
   `LEARNING_EVALUATOR_AUTHORIZED = true` and `LEARNING_EVALUATOR_CORE` (the core checkout on that
   runner). Then add a profile (`provider: local-cli`, `settings.solver: claude-code`, a budget)
   and enable `evaluator` in `meta/learning.json` — only when a paid evaluation budget is
   authorized. Solvers are programs in `ci/learning/solvers/` chosen by name
   (`ci/learning/providers.py`); `scripted-fixture` is a model-free pipeline test for the
   bootstrap families. A maintainer may instead run the same evaluator on their own machine
   (`SIGABA_LEARNING_EVALUATOR=authorized python3 -m ci.learning.cli evaluate ... --core <core>
   --workdir <dir> --publish`) and push the records to `learning-records`.
3. Certification needs an environment whose core has the benchmark commands
   (`SigabaNeo.Trusted.GeneratorCheck`): add it to `env/environments.json` as for any core
   release.
4. Approve families (`families` in `meta/learning.json`: the Lean adapter's module and name,
   its source digest, `seed_bits`, `entropy_bits`, `max_levels`, group and assessment split)
   after reviewing the adapter for vacuity and meaning. A family is approved before any
   generator uses it.

Run locally (no model calls): `python3 -m ci.learning.cli status --base .`,
`python3 -m ci.learning.cli report --records <learning-records checkout> --out report/`, and
`python3 -m unittest discover -s ci/learning/tests -t .`.
