---
title: Leaf lemma (C1) - smoothness of [I_l (x) B | W], the encryptor's own setup, and the leaf view over Def_SuccinctLWE's setup
refs: [note:pq-we-encryptor-setup-flooding, note:pq-we-leaf-view-no-trapdoor, definition:SuccinctLWE, definition:WE_EncryptorSetup, theorem:AdvancedEncryption.WE.LeafView.encryptorSetup_close, theorem:AdvancedEncryption.WE.LeafView.succ_gadget_exists, theorem:AdvancedEncryption.WE.LeafView.leafView_close_succinct, theorem:AdvancedEncryption.WE.LeafView.trapdoorLaw_tail, theorem:AdvancedEncryption.WE.LeafView.leafView_close_encryptor, definition:WE_EncryptorLeafSetup, theorem:AdvancedEncryption.WE.LeafView.trapdoorLaw_flood_close, theorem:AdvancedEncryption.WE.LeafView.leafView_close_zmod]
tags: [witness-encryption, lemma, trapdoor-sampling, smoothing, leftover-hash]
---
This note continues `pq-we-encryptor-setup-flooding` ("What remains", items 1 to 3) and item 2 of
`pq-we-leaf-view-no-trapdoor` ("Instantiation with `Def_SuccinctLWE`'s law"). All three items
are now theorems with proofs.

## Proved

**Smoothness (item 1), self-contained proofs (PR #38).**

* `dualMassE_stacked_le` (any `q`): `Λ^⊥([I_ℓ ⊗ B | W])` contains `Λ^⊥(B)^ℓ ⊕ Λ^⊥(W)`, so
  `dualMassE + 1 ≤ (S_B + 1)^ℓ (S_W + 1)`, where `S_M` is the integer-vector bound of
  `SigabaNeoStd`'s `dualMassE_le` (sum of `e^{−πτ²‖v‖²/q²}` over nonzero `v ⊥ ker M`). In the
  proof, an integer vector orthogonal to `ker [I ⊗ B | W]` has every block orthogonal to `ker B`
  and its `W` part orthogonal to `ker W`, and the weight factorizes over the blocks.
* `card_bad_stacked` (`q` prime, `τ ≥ 1`, `2τ ≤ q`, `3 m e^{−πτ²} ≤ 1/2`): at most a
  `4(ℓ+1)(12 m e^{−πτ²} + (q^n + q^{ℓn})(4/τ)^m)` fraction of uniform pairs `(B, W)` has
  `dualMassE([I_ℓ ⊗ B | W], τ) > 1/2`. Markov per block (`ε = 1/(4(ℓ+1))`, so
  `(1+ε)^{ℓ+1} ≤ 3/2`), with `sum_dualMassE_le`'s counting generalized to any `n`, `m` and prime
  `q`. So the block structure does reduce to the uniform case, block by block. The cost is the
  `q^{ℓn}(4/τ)^m` term: `W` alone must be smooth, which needs `m log(τ/4) ≳ ℓ n log q`. The gadget
  trapdoor of `W` needs `m ≥ ℓ n k` columns anyway.

**The encryptor's setup (items 2 and 3).** `Def_WE_EncryptorSetup` defines the sampler:
`W = [A | H − A R]` (`H = gadget (ℓn) k q`, `A` uniform, `R` uniform binary, `m = mb + ℓnk`) with
the short preimage map `dOf(v) = [R x; x]` (`x` the bits of `v`, `|dOf(v)_j| ≤ ℓnk`), and `T` by
flooding (`floodT`).

* `encryptorSetup_close` (sketch over the proved `trapdoorLaw_flood_close`; the count of
  `card_bad_stacked` is inlined): the encryptor's `(B, W, T)` is within
  `ℓnk(2θ + 6M'4^{−M'} + 3·2^{M'}4^{−M'²}) + 4(ℓ+1)(12 m e^{−πσ²} + (q^n + q^{ℓn})(4/σ)^m)
  + 2 · ℓnk √(q^{ℓn}/2^{mb})/2` of `Def_SuccinctLWE`'s `(B, W, T)` (`chalLaw`), with
  `b = ℓnk`, `M' = ℓm + m`. In the solution, `closeTo_genW` shows that `W` is within
  `ℓnk √(q^{ℓn}/2^{mb})/2` of uniform (leftover hash lemma). It is used twice: once for the
  probability of the non-smooth event, once to replace `W` after `T` no longer uses `R`.

**Plugging into the leaf lemma (item 2 of `pq-we-leaf-view-no-trapdoor`).**

* `succ_gadget_exists`: a `GadgetMatrix` over `ℤ_q` with `G = gadget n k q` (the `G` of
  `Def_SuccinctLWE`) and binary `G⁻¹`, `dec`, entries `≤ 1`, whenever `q ≤ 2^k` (true for
  `k = ⌈log₂ q⌉`). Complete proof.
* `leafView_close_succinct` (sketch over `leafView_close_zmod`): the leaf view with the setup kernel
  `S B = (row blocks of W ← uniform, T ← trapdoorLaw p B W)`, `good(T)` = "`T ≠ none`, entries
  `≤ E_T`", the blocks `T_B[i,j]`, `T_W[j]` of `T` and `Γ.G = G`. The block identity is proved on
  the support: outputs of `Trapdoor.preimage` solve `[I ⊗ B | W] T = I ⊗ G` column by column.
* `leafView_close_encryptor` (sketch over the two theorems above): the same two views with the
  **encryptor's own** `(W, T)` (`Def_WE_EncryptorLeafSetup`'s `leafSetupEnc`: no trapdoor for
  `B`, `W` with a gadget trapdoor, `T` by flooding) are within `2 · (bound of
  encryptorSetup_close) + 2 · m √(q^n/2^m)/2`. The draws of the key bits and of `(W, T)` commute,
  so each view is the joint law of `(B, W, T)` followed by a common continuation. That joint law
  is `encLaw` or `chalLaw`. This is the statistical half of the leaf lemma (C1) for a WE
  encryptor that has no common reference string.

**Tail bound (gap 3 of `pq-we-leaf-view-no-trapdoor`).**

* `trapdoorLaw_tail` (self-contained): on smooth `(B, W)`, `T ← trapdoorLaw p B W` has a column of
  norm `≥ σ√M'` with probability at most `ℓnk · 3 · 2^{−M'}` (`cosetGauss_tail` and the union
  bound `ev_sampleOptList_exists`). Every entry is at most the column norm, so `E_T := ⌈σ√M'⌉`
  passes the leaf lemma's check except with that probability plus `Pr[T = none]`.

## What remains

1. **Tail bound for the encryptor's own `T`.** `trapdoorLaw_tail` is about the challenger's `T`.
   For the encryptor's flooded `T` (correctness of the scheme), the same bound holds up to the
   distance of `encryptorSetup_close`. A direct proof also works: `y` has Gaussian tails and the
   added `dOf` part has entries `≤ ℓnk`. Neither is formalized.
2. **`T = none` for a uniform `W`.** The tail bound is now proved (`trapdoorLaw_tail`, above), but
   `T = none` exactly when some coset is empty, that is, when `[I ⊗ B | W]` is not onto
   `ℤ_q^{ℓn}`. Smoothness does not exclude this. For the encryptor's `W` it cannot happen (`dOf`
   is a preimage map). For a uniform `W` it has probability at most `q^{ℓn}/q^m` (a nonzero `y`
   with `yᵀW = 0`), which is not formalized. It matters only for correctness and for the
   tightness of the reduction (`pq-we-leaf-view-no-trapdoor`, gap 3).
3. **The full instance and the reduction.** `encLaw` gives `(B, W, T)`. The second component
   `b = sᵀB + e` (or uniform) depends only on `B`, so the same bound holds for `(B, b, W, T)` and
   for `Def_SuccinctLWE`'s encoded laws. That data-processing step is not formalized.
4. **Parameters (gap 4).** With security parameter `κ`, for every error term to be at most
   `2^{−κ}`:
   * flooding: `θ ≤ 2^{−κ−1}` needs `σ ≳ 2π M'² b · 2^{κ}` with `b = ℓnk` and `M' = (ℓ+1)m`,
     so `log σ ≈ κ + 2 log M' + log(ℓnk) + 3`. The other flooding terms are `2^{−Ω(M')}`;
   * smoothness: `e^{−πσ²}` is negligible; `(q^n + q^{ℓn})(4/σ)^m ≤ 2^{−κ}/(8(ℓ+1))` needs
     `m (log σ − 2) ≥ ℓ n log q + κ + log(16(ℓ+1))`, which holds with `m ≥ ℓnk` once
     `log σ ≥ 4 + κ/m`;
   * leftover hash: `mb ≥ ℓ n log q + 2κ + 2 log(ℓnk) + 2`;
   * `m = mb + ℓnk ≈ 2ℓ n log q + 2κ`, which also meets `Def_SuccinctLWE`'s `m ≥ 2n⌈log q⌉`;
     `σ² ≥ n k²` holds trivially;
   * the leaf boxes: `E_T ≈ σ√M'` enters `errBound k ((m + ℓ) E_T) φ`, so the big-box width `Bb`
     and `q` grow by about `log σ ≈ κ + O(log(ℓ m n k))` bits over the no-flooding design. This is
     the price of having no trapdoor for `B`;
   * the `ℤ_q` box-sampler abort probability (the analogue of `leafKey_abort_le`) matters only for
     correctness, since the real and simulated laws agree including aborts. It is not formalized.
5. **Unchanged.** The computational half of (C1) and the internal-node step (C2) of
   `pq-we-tree-candidate-crux` (FE-hard) are unchanged. This leaf lemma is a reusable piece, not a
   WE scheme.
