---
title: The PLR hop of positional masked GGH15 - a rank obstruction, a correctness fix, and the ERASE lemma
refs: [definition:WE_CircuitSAT, note:pq-we-witness-prf-masked-evaluator, note:pq-we-split-lemma-attempts, note:pq-we-hybrid-count-barrier]
tags: [witness-encryption, ggh15, candidate, barrier]
---
This note records an analysis of the positional-local-reprogramming (PLR) hop for the positional
masked γ⊗-GGH15 candidate (open PR "pq-we-masked-evaluator-mechanisms"; masked evaluator of
`pq-we-witness-prf-masked-evaluator`). Everything here is an informal argument, not a Lean proof.
The rank obstruction in §1 rests on CVW18's heuristic Claim 9.4 and has **not** been checked
experimentally.

## 1. The PLR hop, as stated, is likely false at polynomial width (rank obstruction)

The hop asks that for every non-witness threshold `t` (`C(x*, t) = 0`) the evaluators `Ô_t` and
`Ô_{t+1}` be indistinguishable, with the hop independent of the statement.

* Take a **true** statement with one clause of the form "`w_{>i} ≠ t*_{>i}`", alive on every
  prefix of length `i`, and the non-witness `t = t*` with `t* = x*·1^{h−i}` and `x*` large.
* Witness paths of the "lt" class evaluate to `m' + small noise`. Over a rectangle `S × U` of such
  paths, the differences `V'[x,u] = y_{xu} − y_{xu0}` factor as `[X_x | e_x]·ΔY`, so
  `rank V' = m + rank{X_x : x ∈ S}`.
* In hybrid `t`, the chain prefix `t_{≤i}` sits in the separate "eq" row block, which adds a
  direction (rank `m + 3`). In hybrid `t+1` that prefix belongs to "lt" and lies in the span of
  the overcomplete lt rows (rank `m + 2`).
* Requirements: `|S|, |U| ≥ t' + m + 1` (so `h ≳ 2 log(t' + m)`), and a CVW18 §9.3-style
  factorization through witness paths.

**Consequence.** A statement-independent PLR hop fails whenever many witnesses sit near the
threshold. Restricting the hop to false statements would make it statement-dependent, which this
problem forbids.

## 2. Correctness issue in the instance of the mechanisms note

With fresh comparator secrets `R_{i,b}` for each bit, `O − ck = r_0 R_z a` depends on the path,
so decryption is not canonical. **The comparator secrets must be bit-independent (`R_i`).**

## 3. Positive result: the ERASE lemma (from LWE, any polynomial width; informal)

**Construction variant.** Comparator rows split per class (the eq chain plus departure classes),
constraint secrets `S'_{i,b}`, and per-class final rows.

**Statement.** If `t` falsifies a clause `k` whose deepest variable is at level `ℓ_k`, then the
whole subtree below `t_{≤ℓ_k}`, including path `t`'s eq leaf, can be replaced by unrelated
pseudorandom values.

**Proof outline.**

1. CVW18 phase 1 strips the CPRF block.
2. Run leaf-first LWE on all `(class, k)` blocks, from level `h` down to `ℓ_k`.
   * LWE secret: `A^{c,k}_i` (uniform, `n' × m`).
   * Public matrices: `S'_{i,b}`, small Gaussians, using CVW18 Lemma 3.9 and the BLMR13 normal form.
   * There are no zero encodings below `ℓ_k`, and each target block has a unique source, so the
     samples are independent.
3. Root-first projection down to level `ℓ_k − 1` (the projection lemma of
   `pq-we-split-lemma-attempts`).
4. One-time pad `c^k_{t<ℓ_k}·U^{eq,k}`, where `c ≠ 0` and the uniform `U` is used only by the eq
   direction.
5. An "unused hidden rows" statistical lemma erases the eq chain below that point.

**Consequence.** The leaf flip `m → m'` of path `t` is provable for every non-witness `t` in
`poly(h)` steps.

## 4. Exact remaining gap: rerouting the chain from `t` to `t+1`

Moving the threshold is a statement-independent class split: one departure class becomes a chain
plus sub-classes, with the same function on witnesses.

* By projection it is provable only when the split depth `r ≤ log2(class width)`. Deeper splits
  are open.
* The rank obstruction of §1 shows that deep splits are visible on true statements. Any proof
  must therefore use the falsity of the statement in a way that does not make the hop
  statement-dependent, or change the construction so that splits stay shallow.

## 5. Other checks

* CVW18 has no general "LWE with correlated secrets" lemma; the closest is Lemma 3.9.
* Its private constrained PRF proof (Lemmas 7.4 and 7.7) performs a PLR-like switch at
  polynomially many points. It works there because evaluations are rounded *oracle* outputs
  carrying fresh flooding noise, which a public GGH15 ciphertext cannot supply.

## 6. Lemmas to formalize (pure linear algebra; not yet in the DAG)

* The rank factorization identity of §1.
* The sibling identity `y_{xb} = y_{xb'} · D_{b'}^{-1} D_b`, under invertibility of `D_{b'}`.
* The unused-rows counting fact of §3, step 5.
