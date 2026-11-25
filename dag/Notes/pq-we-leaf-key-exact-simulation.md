---
title: Leaf lemma (C1), statistical half - the false-leaf key is simulated exactly by box rejection
refs: [definition:SuccinctLWE, definition:WE_CircuitSAT, theorem:AdvancedEncryption.WE.Wee.leaf_trapdoor_norm, theorem:AdvancedEncryption.WE.Leaf.leafKey_apply_some, theorem:AdvancedEncryption.WE.Leaf.leafKey_real_eq_sim, theorem:AdvancedEncryption.WE.Leaf.leafKey_abort_le, theorem:AdvancedEncryption.WE.Leaf.leafKey_sim_of_false_leaf]
tags: [witness-encryption, lemma, trapdoor-sampling]
---
This note records the statistical half of the leaf lemma (C1) of `pq-we-tree-candidate-crux`.
The algebraic half is `AdvancedEncryption.WE.Wee.leaf_trapdoor_norm`: for a false leaf,
`A_φ − G = B R_φ − G` with `R_φ` short. Here we show that the leaf key
`K_leaf ∈ [B | A_φ − G]^{-1}(u)` sampled with a trapdoor of `B` has **exactly** the same law as
the one sampled with `R_φ` alone. No Gaussian smoothing and no statistical distance are needed.

## Choice of the sampler

The scheme samples `K_leaf` with **box rejection** (Lyubashevsky-Wichs PKC'15 with uniform boxes;
`SigabaNeo.Lattices.boxSample`, as in PE's `keyLaw_real_eq_sim`). The algorithm makes one try with
the public map `x ↦ B x`, the decomposition `y ↦ G⁻¹(−y)` (gadget map `z ↦ −G z`) and a trapdoor
`T` of `[B | A]`, meaning `B T(z) = (A + G) z`:

* draw `p` uniform in a big box; set `z = G⁻¹(−(u − B p))` and `x = p − T z`;
* output `(x, z)` if `x` is in the small box, and abort otherwise.

An output satisfies `B x + A z = u`.

* Real: `B Tm = G`, where `Tm` is a gadget trapdoor of `B` (e.g. `GTrapdoor`), gives
  `T = Tm · G⁻¹(A + G)` (for `A = A_φ − G`, this is `Tm · G⁻¹(A_φ)`).
* Simulated: `A = B R − G` gives `T = R`.

## Proved (all `ACCEPTED` locally, self-contained proofs)

* `leafKey_apply_some`: for every trapdoor `T` covered by the boxes, the probability of an output
  `(x, z)` is explicit: `1/|Big|` on `{x ∈ Small, z a decomposition, B x + A z = u}` and `0`
  elsewhere.
* `leafKey_real_eq_sim`: over any commutative ring, if `B Tm = G` and `A = B R − G`, the real law
  equals the simulated law, provided both shifts are covered.
* `leafKey_abort_le`: over `ℤ_q[X]/(X^N+1)`, with a trapdoor matrix whose rows have norm `≤ ρ`,
  `k N ρ ≤ τ`, the small box of radius `≥ 2^{Bb−1} − 1 − τ` and the big box of `Bb` bits, the
  abort probability is at most `2^{−κ}` when `m N (4τ + 1) 2^κ ≤ 2^{Bb}`.
* `leafKey_sim_of_false_leaf` is the leaf lemma's statistical half, end to end. It takes the
  ℓ-succinct LWE block identity, bit attributes, input trapdoors with entries `≤ E`, `φ(w) = 0`,
  and a gadget trapdoor `Tm` of `B` with entries `≤ E_T`. The leaf key sampled with `Tm` has the
  same law as the one sampled with `R_φ = evalSim(…)`. The coverage conditions are
  `s + kN·errBound(kN, E, φ) ≤ 2^{Bb−1} − 1` and `s + (kN)² E_T ≤ 2^{Bb−1} − 1`.

The equality holds as laws on `Option (key)`, so the abort event matches too. Any
post-processing, such as retrying on abort or outputting ⊥, therefore keeps it exact.
The statement holds pointwise for every outcome of setup `(B, W, T_B, T_W, R, Tm)` satisfying the
hypotheses.

## What remains (not covered here)

1. **Several columns.** A matrix target `U` is sampled one column at a time with independent coins.
   The law is the product of the per-column laws, so the equality follows column by column. This
   step is not formalized.
2. **Setup distribution.** The scheme samples `B` together with a gadget trapdoor `Tm`, while the
   ℓ-succinct LWE challenger samples `(B, W, T)` itself, with no `Tm`. The scheme's
   `(B, W, T_B, T_W)` must therefore follow the assumption's law (or be statistically close to it).
   Two cases:
   * If `T` is sampled with `Tm`, this is again a "sampler law independent of the trapdoor"
     statement, now for `[I ⊗ B | W]^{-1}(I ⊗ G)`. The box sampler could give it exactly, but
     only if the assumption's `T` distribution is itself the box law. `Def_SuccinctLWE` uses
     Wee's Gaussian `T`, so that would need a box-variant assumption or a smoothing argument.
   * Otherwise the real scheme must not need `Tm`, and then the real leaf key needs another
     trapdoor.

   This is the main open point. It concerns the *real* scheme's setup, not the leaf.
3. **Attribute encoding.** The simulated attribute matrix `A = Σ w*_i W_i + B R` must be close to
   the real one: a leftover-hash or LWE hop, not formalized here.
4. **The norm hypothesis `hE`.** The entries of `R T_W[j] − Σ_i w_i T_B[i,j]` are bounded by `E`
   only with high probability when `T` is Gaussian. This needs a tail bound, or a box-sampled `T`
   with a deterministic bound.
5. **Parameters.** Coverage forces `2^{Bb} ≳ m N (4τ + 1) 2^κ` with
   `τ ≥ max(kN·errBound(kN, E, φ), (kN)² E_T)`. Since `errBound` grows like `(kN)^{depth(φ)}`, the
   leaf key is large: its entries are up to about `2^{Bb−1}`. This affects decryption noise and
   the modulus `q > 2^{Bb}`. The cost is the usual BGG+ one, polynomial for depth `O(log)`, and
   must be checked against `Def_WE_CircuitSAT`'s `2^12` gates.
6. **The computational half of (C1)**: the succinct-LWE hop on the leaf's LWE part and the
   leftover hash lemma for the message. These are not addressed here.
