---
title: Post-quantum WE for Circuit-SAT from falsifiable assumptions - summary of results and open problems (November 2026)
refs: [definition:WE, definition:WE_CircuitSAT, definition:SuccinctLWE, definition:DecomposedLWE, note:pq-we-route-survey, note:pq-we-hybrid-count-barrier, note:pq-we-function-hiding-crux, note:pq-we-evaluation-oracle-crux, note:pq-we-affine-syzygy-barrier, note:pq-we-linear-hop-barrier, note:pq-we-gap-structure-routes, note:pq-we-non-lattice-algebras, note:pq-we-reduction-query-flattening, note:pq-we-witness-prf-masked-evaluator, note:pq-we-masked-evaluator-mechanisms, note:pq-we-plr-hop-rank-and-erase, note:pq-we-shallow-split-arrangements, note:pq-we-multipass-ggh15, note:pq-we-ggh15-vocabulary-open-lemmas, note:pq-we-leaf-setup-assembly, note:we-circuitsat-bruteforce-explicit-cost]
tags: [witness-encryption, summary, open-problem]
---
This note summarizes the Design-AI work on the problem `Def_WE_CircuitSAT`. The target is
witness encryption for NAND-circuit satisfiability, with 128-bit witnesses, `2^12` gates and
`λ = κ = 128`, built from post-quantum, falsifiable assumptions whose instances do not depend on
the statement. iO routes, evasive LWE and local mixing are excluded. Details are in the referenced
notes and their theorems.

## 1. Bottom line

* **No complete construction from the allowed assumptions.** No submission with a polynomial
  cost is proved. As far as we found, none is known in the literature either.
* **A complete assumption-free baseline exists**: brute-force WE, with an explicit cost
  `N ≈ 2^{188}` and a complete proof (`we-circuitsat-bruteforce-explicit-cost`). Any real
  construction must beat this cost.
* **The best candidate is MP2/MP3** (`pq-we-multipass-ggh15`). It is a multi-pass, masked
  γ⊗-GGH15 WE of about `2^{97}` bits that relies on LWE only.
  * Canonical decryption is proved in Lean.
  * No known attack applies on false statements (cryptanalysis note "pq-we-mp2-cryptanalysis",
    open PR).
  * One lemma is missing (§4).
* **Honest assessment.** MP2/MP3 is a variant of the GGH15 witness encryption of the literature
  (CVW18 Construction 10.1; VWW22 and Tsabary 2022 prove such schemes from evasive LWE). Its
  missing lemma sits where those works invoke evasive LWE. The progress is that the gap is now a
  specific, local, statement-independent LWE-type claim about one structure, rather than a general
  evasive assumption.

## 2. Assumptions reproduced from the literature

* `Def_SuccinctLWE`: Wee, CRYPTO 2024, as Assumption 1 of arXiv 2603.16117.
* `Def_DecomposedLWE`: Abram–Malavolta–Roy, ePrint 2025/339, Definition 4.1.

Both were checked by an independent read-back against the source text.

## 3. Barriers (why the problem is hard)

| Barrier | Note |
| --- | --- |
| A poly-hop proof under statement-independent assumptions puts `L` in SZK; about `2^{128}` witness-indexed hops are needed, hence about 384-bit premises | `pq-we-hybrid-count-barrier` (plus the `stat_hops_carry` theorem) |
| Hops that change the function inside a key need function hiding, hence FE, hence iO | `pq-we-function-hiding-crux` |
| The core object is a public evaluator for `F(w) = ⌊sᵀA_{U_w}⌉` | `pq-we-evaluation-oracle-crux` |
| Data-only hops with constant-degree noisy-linear decryption are impossible | `pq-we-affine-syzygy-barrier`, `pq-we-linear-hop-barrier` |
| NP-hard gap structures, non-lattice algebras (LPN, codes, group actions, Goldreich PRG, MQ) and rewinding reductions give no escape | `pq-we-gap-structure-routes`, `pq-we-non-lattice-algebras`, `pq-we-reduction-query-flattening` |
| Read-once GGH15 walks with single-prefix flips need width `≥ 2^{64}` (fixed-cut lemma, Lean) | `pq-we-shallow-split-arrangements` |

## 4. The candidate line and its exact gap

1. **Witness PRF from a constrained PRF plus a mask** (`pq-we-witness-prf-masked-evaluator`).
   The reduction to WE is proved in Lean. Naive BV15-type instantiations leak the mask.
2. **Positional local reprogramming** (`pq-we-masked-evaluator-mechanisms`) leads to masked
   γ⊗-GGH15.
3. **Single pass** (`pq-we-plr-hop-rank-and-erase`). A rank obstruction applies to deep splits.
   The ERASE lemma is provable from LWE at polynomial width.
4. **Multi-pass MP2/MP3** (`pq-we-multipass-ggh15`). Equality clauses between copies make every
   mixed string non-zero, and there are no honest rectangles (Lean).
5. **Vocabulary and open nodes** (`pq-we-ggh15-vocabulary-open-lemmas`): `Def_GGH15`,
   `Def_WE_MaskedGGH15`, open theorems `plr_hop`, `masked_two_vector` and `overcomplete_cut`.
6. **Statistical leaf step** (`pq-we-leaf-setup-assembly` and its predecessors). An exact
   box-rejection simulation, with smoothing and setup closeness proved.

**The gap** (open PR "pq-we-two-pass-reroute"): the threshold reroute of MP2/MP3. It reduces to
`2(n−j)` instances of a *masked-leak lemma*. A consistency barrier shows that no CVW18-type LWE move
proves it, so a new "bilinear" LWE argument is needed. The weaker **equality-cube flip** lemma
(regime (d) of `pq-we-multipass-ggh15`) concerns a class with no witness below. Neither the
consistency barrier nor the SZK barrier applies to it, so it is the most promising next target.

## 5. Process notes

* Gate pitfalls found along the way:
  * SigabaNeoStd modules not reachable from the root were not built; a fix, env-2 with core
    v0.2.3 whose image carries every std module, is an open PR in this repository.
  * `import Mathlib` fails in env-2; import specific modules, including tactic modules.
  * Inductive types get `ctorIdx` (`implemented_by`); use `Fin n` instead.
  * Compiled recursive definitions must be marked `noncomputable`.
* Papers were read from source texts: arXiv through its API, ePrint through a real browser
  (`.claude/skills/sigaba-papers`).
