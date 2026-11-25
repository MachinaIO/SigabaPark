---
title: The WE encryptor's own succinct-LWE setup - T sampled by flooding with a trapdoor of W only
refs: [note:pq-we-leaf-view-no-trapdoor, definition:SuccinctLWE, theorem:AdvancedEncryption.WE.LeafView.floodColumn_close, theorem:AdvancedEncryption.WE.LeafView.trapdoorLaw_flood_close, theorem:AdvancedEncryption.WE.LeafView.leafView_close_zmod]
tags: [witness-encryption, lemma, trapdoor-sampling, flooding]
---
This note continues `pq-we-leaf-view-no-trapdoor`, item 1 (gap 1b). `Def_WE_CircuitSAT` has no
common reference string, so the WE encryptor must sample the succinct-LWE instance `(B, W, T)`
itself, with a law close to the challenger's (`Def_SuccinctLWE`, `trapdoorLaw`). With the
attribute-0 redesign the leaf key no longer needs a trapdoor of `B`. Here `T` does not need one
either.

## Construction

`B` is uniform, with no trapdoor. `W ∈ ℤ_q^{ℓn×m}` comes with a short preimage map `d_W`
(`W d_W(v) = v`, `|d_W(v)_j| ≤ b`), for example an MP12 gadget trapdoor `W = [W̄ | H − W̄ R_W]`.
Each column of `T`, with target `t` (a column of `I_ℓ ⊗ G`), is the flooding sample

    y + [0; d_W(t − M y)],   y ← D_{Z^{ℓm+m}, σ},   M = [I_ℓ ⊗ B | W].

## Proved (`ACCEPTED` locally, self-contained)

* `floodColumn_close`: for **any** `M ∈ ℤ_q^{n×m}` with a short preimage map `d`, the law of
  `y + d(u − M y)` is within `2θ + 6 m 4^{−m} + 3·2^m 4^{−m²}` of the coset Gaussian
  `D_{Λ^⊥_u(M), τ}`, where `θ = π m (b² + 2 τ m b)/τ²`. The conditions are `τ ≥ 1`,
  `τ √m + b ≤ τ m` and `dualMassE M τ ≤ 1/2`. This generalizes `SigabaNeoStd`'s
  `Trapdoor.Family.colLaw_close`, which is the case `M = Bmat` at the family's parameters. The
  proof is the same, with the constants turned into hypotheses.
* `trapdoorLaw_flood_close`: for `Def_SuccinctLWE`'s parameters `p`, any `B`, and `W` with a short
  preimage map, the flooded `T` is within `ℓ n k · (2θ + 6 M' 4^{−M'} + 3·2^{M'} 4^{−M'²})` of
  `trapdoorLaw p B W`, with `M' = ℓm + m`. It needs `σ ≥ 1`, `σ √M' + b ≤ σ M'` and smoothness of
  `Λ^⊥([I_ℓ ⊗ B | W])` at `σ`. The `B` blocks of the preimage map are zero.

## Parameters

`θ` is small only when `σ ≳ π M'^2 b · 2^κ` (flooding). `Def_SuccinctLWE`'s strength `H` bounds
`σ` only from below, so the claim is unchanged. The cost is a large `T`: with high probability its
entries are below `σ √M'`. That bound is the `E_T` of `leafView_close_zmod`, so the leaf boxes and
`q` grow by about `κ + O(log)` bits. `W` needs `m ≥ ℓ n ⌈log q⌉ + m̄` columns for its gadget
trapdoor, which `Def_SuccinctLWE` allows (`m ≥ 2 n ⌈log q⌉` is only a lower bound).

## What remains for gap (1b)

1. **Smoothness for most `(B, W)`**: `Pr[dualMassE([I_ℓ ⊗ B | W], σ) > 1/2]` is small. The block
   form is not uniform, so `SigabaNeoStd`'s `card_bad_le` does not apply directly. The natural
   argument is that `sᵀ[I ⊗ B | W]` has a uniform `W` part for every `s ≠ 0`. The same statement
   gives the tail bound of gap (3) in `pq-we-leaf-view-no-trapdoor`.
2. **`W` with a trapdoor is close to uniform**: the leftover hash lemma on `W̄ R_W`, as in
   `SigabaNeoStd`'s `closeTo_genB` or with `closeTo_binaryHash_bind`.
3. **Assembly**: `(B, W, T)` from the encryptor is within (2) + (statement above) + Pr[not
   smooth] of the challenger's law. The leaf view of `leafView_close_zmod` is then within those
   errors plus twice the leftover-hash bound when the setup is the encryptor's instead of the
   challenger's.
