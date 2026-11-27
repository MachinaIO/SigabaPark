---
title: Post-quantum WE for Circuit-SAT from falsifiable assumptions - summary of results and open problems (late November 2026)
refs: [definition:WE, definition:WE_CircuitSAT, definition:WE_CircuitSAT_Capped, definition:WE_MaskedGGH15, note:pq-we-summary-2026-11, note:pq-we-hybrid-count-barrier, note:we-circuitsat-bruteforce-explicit-cost, note:pq-we-xwe-from-bgg-abe-design, note:pq-we-xwe-per-item-cost, note:pq-we-ksplit-xwe-routes, note:pq-we-two-input-abe-secret-key, note:pq-we-multipass-ggh15, note:pq-we-mp2-cryptanalysis, note:pq-we-two-sided-lwe, note:pq-we-tlwe-masked-ggh15-leaf, note:pq-we-ecf-overcomplete-succinct-levels, note:pq-we-hinted-lattice-assumptions, note:pq-we-direct-algebraic-languages, note:pq-we-native-hop-designs, note:pq-we-zero-entry-crossing, note:pq-we-exposed-root-reachable-lemma, note:pq-we-point-insertion-frontier, note:pq-we-apg-width-ring-analysis, note:pq-we-class-lock, note:pq-we-non-lattice-ggh15-analogues, note:pq-we-hybrid-tool-combinations]
supersedes: pq-we-summary-2026-11
tags: [witness-encryption, summary, open-problem]
---
This note summarizes the Design-AI work on post-quantum witness encryption for NAND
Circuit-SAT (128-bit witnesses, `2^12` gates, `λ = κ = 128`) since `pq-we-summary-2026-11`. The
allowed assumptions are falsifiable, statement-independent and post-quantum; iO and its
relatives, evasive LWE and local mixing are excluded. Details and proofs are in the referenced
notes and their theorems. Open PRs are cited by number only. The work is paused at this point.

## 1. Bottom line

* **No efficient construction with a complete proof.** Nothing below the cost cap `2^{100}` is
  proved, and no design examined reaches the cap even with its open lemma granted.
* **The problem was tightened** (`Def_WE_CircuitSAT_Capped`). The uncapped `Def_WE_CircuitSAT`
  admits submissions that are useless as WE. These include brute force (about `2^{188}`), padding
  the message beyond a sequential adversary's reach (about `2^{128.6}`,
  `pq-we-xwe-per-item-cost`), and enumeration-based XWE (about `2^{145}`). The capped problem
  adds the proposition `cost ≤ 2^{100}`, which also bounds the ciphertext length.
* **Provable but too expensive:** XWE from Ring-LWE BGG+ ABE, at about `2^{145.5}` in the worst
  case. Finer splits need a 2-input ABE from plain LWE, which is not known.
* **The best efficient-looking line (GGH15 with pads) is blocked twice.** Its security proof
  meets a proved lock, and its size is above the cap.
* **Lattices appear necessary, and no other family can carry the construction.** No non-lattice
  family and no combination of tools does better than lattices alone.

## 2. The cost cap

`Def_WE_CircuitSAT_Capped` is the uncapped problem with a third proposition
`WE.cost impl ≤ 2^{100}`. Its checks: `prop_costBound` and `not_costBounded_of_enc_time`.

## 3. XWE (enumeration of half the witness)

| Result | Note |
| --- | --- |
| Ring BGG+ instantiation: `N ≈ 2^{147.7}` (`d = 2^{25}`, `log q ≈ 2.9·10^5`, keys `2^{57}`, ciphertexts `2^{71}`); abstract hybrid security proved | `pq-we-xwe-from-bgg-abe-design` |
| Per-item cost: noise bounded by the asymmetric level `L`; worst case `N ≈ 2^{145.5}`; `L = 1` gives about `2^{111}`; the premise can be lowered from 437 to 334 bits | `pq-we-xwe-per-item-cost` |
| `k`-way splits need `(k−1)`-input ABE; the table bound `k·2^{m/k}`; a layered chain helps only bounded-width verifiers | `pq-we-ksplit-xwe-routes` |
| Secret-key 2-input ABE: additive slot secrets leak (`rect_leak`); the bilinear candidate C2 is unproven (about `2^{123.6}` if proved) | `pq-we-two-input-abe-secret-key` |

## 4. The GGH15-with-pads line (MP2, APG, APG′-direct)

**Construction.**
* γ⊗-GGH15 encodings of the Tseitin CNF branching program, with level secrets
  `diag(R_i, M_{i,b}⊗S'_{i,b}, pad block)`.
* APG′-direct publishes the single exposed row `R = P·A_0` as its left vector. Decryption gives
  `R·D_w = mask + (constraint term) + noise`, and the ciphertext is `⌊mask⌉ + μ`.
* The CPRF block and the second left vector of the earlier designs turned out to be unnecessary
  (`pq-we-point-insertion-frontier`).

**Proof plan.**
* Erase the `2^{128}` candidates in lexicographic order.
* The erased set is a union of at most 128 subcubes, held by pad slots.
* Each hop is either a pad merge (PM, value-preserving) or a point insertion (PI, which uses
  `C_Ψ(k) ≠ 0`).
* About `2^{135}`–`2^{154}` hops, so premises of about 420–470-bit LWE.
* Evasive LWE is avoided because each hop is local and statement-independent, at the price of
  exponentially many hops.

| Step | Status | Note |
| --- | --- | --- |
| Zero-entry crossing (the step CVW18 cannot take) | Localized to "Lemma 4.4 with one exposed root row" | `pq-we-zero-entry-crossing` |
| Exposed-root lemma, and cover flips / PM for shared pad secrets (APG′) | **Proved from LWE** (Bonsai on short-lift complements plus smudging) | `pq-we-exposed-root-reachable-lemma` |
| PI | Open. Decomposed into LEN and NCF; every proved move keeps an alive-prefix invariant | `pq-we-point-insertion-frontier` |
| Class lock | **Proved**: no walk of class-covered moves (all proved moves, and also LEN) reaches the final hybrid, for any slot count, hop count or erasure order, when the witness levels come first | `pq-we-class-lock` |
| Other level orders | Open PR #118: the lock persists with pinned levels; one escape via unit-propagation refutations from a NOT-shaped output; not completed | — |
| Size | **Above the cap.** Pad width must be about `2^{35}`–`2^{41}` (CVW18 Lemma 3.9); rings are broken (`ring_kernel_break`); modules need an unproved premise; at least `n` cube slots are needed. Best heuristic size `≈ 2^{100.5}` bits, with encryption work `≈ 2^{114.5}` | `pq-we-apg-width-ring-analysis` |

The earlier MP2/MP3 design (`pq-we-multipass-ggh15`) has the same size problem. Its masked-leak
lemma `ML_i` is blocked for trapdoor-holding reductions (`pq-we-two-sided-lwe`). Neither succinct
LWE, TLWE nor hinted lattice assumptions supply it (`pq-we-ecf-overcomplete-succinct-levels`,
`pq-we-tlwe-masked-ggh15-leaf`, `pq-we-hinted-lattice-assumptions`).

## 5. Other routes, all closed

| Route | Verdict | Note |
| --- | --- | --- |
| Additive encodings of NP-complete languages (regular SD, exact cover, subset sum, MQ ideals, group actions) | Broken by `nand_gadget_affine_closure` | `pq-we-direct-algebraic-languages` |
| Native-hop direct lattice designs (wire-indexed systems, Kronecker walks, circular GSW, compute-and-compare) | Broken or reduce to APG | `pq-we-native-hop-designs` |
| Non-lattice GGH15 analogues (codes/LPN, rank metric, group actions, tensor isomorphism, MQ) | Dead. LPN noise compounding allows at most about 74 levels (`chain_noise_bias`); abelian paths are affine (`abelian_path_rectangle`); Kilian randomization telescopes | `pq-we-non-lattice-ggh15-analogues` |
| Tool combinations (garbling, group actions, LPN, SPHF, local PRGs, compute-and-compare) | Dead or no gain. Interface dichotomy: clear interfaces reduce to unpredictability, hidden ones need a lattice carrier | `pq-we-hybrid-tool-combinations` |
| Per-path noise as LWE noise with TLWE hints | Unobtainable: at most `N` paths of an `N`-bit ciphertext can be locally fresh; the witness-entry trilemma (open PR #119) | — |

## 6. Where the problem now stands

Two structural obstacles recur across all routes:

1. **Per-path freshness.** A polynomial-size ciphertext has too little independent randomness for
   `2^{128}` paths. Proofs therefore need exponentially many hops, each re-encoding the hybrid
   (PR #119; `pq-we-native-hop-designs`).
2. **Class-crossing hops.** In the pad framework, the step that uses the falsity of the statement
   must reuse a cover that is alive on other witness prefixes as a pad for one prefix
   (`pq-we-class-lock`). No LWE technique available here performs such a step.

Ways forward, none of them started:

* a new statement-independent re-encoding step between positional hybrids;
* level orders that escape the class lock (PR #118);
* GGH15 chains of fewer than about `2^9` levels, or trapdoors with `m = O(N)`, to meet the size
  cap.
