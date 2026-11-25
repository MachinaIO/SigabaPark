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

## GitHub settings (maintainers)

The workflows assume these settings. Without them the gate is not a boundary.

1. **Permissions.** Nobody but the maintainers has write access; agents and people work from
   forks. Settings → Actions → General: workflow permissions "Read repository contents";
   "Require approval for all outside collaborators" for fork pull request workflows (the gate uses
   `pull_request_target`, which does not need it, but other workflows would). While the
   repository is private, allow forking and "Run workflows from fork pull requests".
2. **The gate's App.** Create a GitHub App with "Contents: read & write", "Pull requests: read &
   write" and "Issues: read & write" (labels), installed on this repository. Create the Environment `gate`, restricted to the `main`
   branch, with the variable `GATE_APP_ID` and the secret `GATE_APP_KEY`. Add the App's bot login
   to `meta/trusted.json` (`accept` and `automerge`) if `formalpedia.yml` is used.
3. **Labels.** The gate labels pull requests `not-accepted` (an author not in
   `meta/trusted.json`), `rejected` (a failing check) and `needs-maintainer` (passed, not on the
   automerge list). It creates them if they are missing; to create them beforehand:
   `for l in not-accepted rejected needs-maintainer; do gh label create "$l" --force; done`.
4. **Ruleset of `main`.** Require a pull request; require the status check `decide` from the
   GitHub Actions app; require the merge queue (squash); require review from code owners; block
   force pushes and deletions. Allow auto-merge in the repository's settings.
5. **Ruleset of `records`.** Only GitHub Actions may push; block force pushes and deletions.
6. **Pages.** Source: GitHub Actions.
7. **Pinned actions.** The workflows pin every action by commit SHA (the version is in a comment),
   and the core pins the image's base by digest. Update a pin deliberately, never to a moving tag.

## Environments and std

A new base environment (a cslib-frontier, Mathlib or Lean update, or a new core tag) is a new entry
in `env/environments.json`, with the image digest that the core's `image` workflow published for
that tag, and its std release added with
`python3 <core>/python/dag_tools.py std-manifest --dag . --tag <tag> --core <core checkout>`.
The `reverify` workflow then checks the existing proofs there.
