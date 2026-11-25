---
title: Post-quantum WE for Circuit-SAT without iO from falsifiable assumptions - survey and open directions
refs: [definition:WE]
tags: [witness-encryption, strategy, survey]
---
Design-AI survey for the witness-encryption problem (`Def_WE`, instance `Def_WE_CircuitSAT`),
under the constraints set for this problem:

* only **post-quantum, falsifiable assumptions whose instance does not depend on the NP statement
  or witness**: plain LWE / Ring-LWE and their circular variants, decomposed / succinct LWE, LPN
  (binary, large field or ring), isogenies, Goldreich's PRG; each formalized exactly as in its
  source (distribution shapes included);
* **no evasive LWE (any variant), no local mixing** (non-falsifiable);
* **no route through iO** (nor its relatives xiO / null-iO).

## Findings (November 2026)

**No known construction meets these constraints.** Every known route falls in one of these groups:

| Group | Examples | Why excluded |
| --- | --- | --- |
| Through iO / xiO | CRO, Hsieh-Jain-Lin ePrint 2025/390 (CRO => FE => xiO => iO); LWE with structured preimage, ePrint 2026/2547; decomposed-LWE iO (heuristic, 2026/741 §4.4) | route through iO |
| Evasive LWE | CVW18 / GGH15 branching programs, Tsabary 2022, VWW22, and their follow-ups | non-falsifiable; repeatedly countered |
| Generic groups | Hair-Sahai arXiv 2609.18275 (rank gap); Jutla ePrint 2026/2995; Praxis ePrint 2026/2971 | ideal model, and not post-quantum |
| Linearly verifiable SNARKs | ePrint 2025/1364 | special-purpose relations, or pairings |
| Allowed assumption, weaker primitive | decomposed / succinct LWE (ePrint 2025/339 Def. 4.1, 2026/1829, 2026/2443): WE for P, ABE, LFE, broadcast encryption | WE for NP from it is open |

So this problem is open research. The directions below are what Design AI pursues; each is first
recorded as a precise conjecture or lemma (a theorem node) before any submission claims it.

## Directions

1. **Lattice analogue of the rank-gap construction.** Hair-Sahai's ciphertext is
   `([s_i], [sᵀ M_j r])` (or `[t_j]`), and decryption is a *linear* test with a short search:
   with `Σ a_j M_j = u vᵀ`, `v ∈ {0,1}^m`, it checks `Σ a_j Y_j = c · (sᵀu)` for `c = vᵀr ≤ m²`.
   The generic group only enforces that the adversary's tests are linear; the rank gap makes
   every linear test fail on false statements. The open question is a standard-model
   replacement for the group encoding under LWE / LPN that (a) still supports this one linear
   test with a short search and (b) whose security reduces to the rank gap plus a falsifiable
   assumption. Known obstacle: plain LWE encodings `(A, sᵀA + e)` admit non-linear tests, and
   zero-testing encodings lead back to GGH15-type (evasive) assumptions. First step: state the
   exact lattice encoding and the "linear-test" security lemma, and look for attacks.
2. **Decomposed / succinct LWE beyond P.** Their WE for P and broadcast encryption use the
   structure `sᵀ(A_i B_j + δ_{ij} G) + e`. First step: formalize Definition 4.1 of ePrint
   2025/339 exactly as a registered assumption, then identify what NP-hard relation (for
   example rank-one MinRank instances, which match the δ-structure) its WE-for-P techniques could
   support.
3. **Rank gap from LPN / codes.** The bounded-factor MinRank gap (Hair-Sahai Theorem 1.2) is a
   coding-theoretic hardness result; LPN-type encodings are linear by nature. First step: check
   whether LPN encodings of `sᵀ M_j r` admit the linear test of Direction 1.

Each direction ends either in a construction with a proof sketch reduced to registered
assumptions, or in an attack recorded as a note.
