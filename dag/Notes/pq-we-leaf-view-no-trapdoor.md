---
title: Leaf lemma (C1) - the real leaf needs no trapdoor for B; real and simulated leaf views are within twice the leftover-hash bound
refs: [definition:SuccinctLWE, definition:WE_CircuitSAT, note:pq-we-tree-candidate-crux, theorem:AdvancedEncryption.WE.LeafView.leafView_close, theorem:AdvancedEncryption.WE.LeafView.leafCover_zmod, theorem:AdvancedEncryption.WE.LeafView.leafView_close_zmod]
tags: [witness-encryption, lemma, trapdoor-sampling, leftover-hash]
---
This note continues `pq-we-leaf-key-exact-simulation` (open PR #24). That note left five gaps for
the statistical half of the leaf lemma (C1) of `pq-we-tree-candidate-crux`. Here gap (1) is
removed for the leaf key, gap (2) is closed, and gap (3) is moved out of the security argument.

## Gap (1): the real leaf key without a trapdoor for `B`

The previous design sampled the real leaf key `K ∈ [B | A_φ − G]^{-1}(u)` with a gadget trapdoor
`Tm` of `B`. The ℓ-succinct LWE challenger gives `(B, W, T)` with no such `Tm`, so the reduction
could not produce the real key.

**Redesign (attribute-0 programming).** The encryptor sets the attribute matrix to
`A = B R` with `R` binary (the BGG+ form of the attribute `0`), so `A_j := A T_W[j] = B (R T_W[j])`.
It evaluates `φ(0)` in the clear:

* if `φ(0) = 1`, then `0` is a witness and the statement is true; witness encryption asks nothing
  of true statements, so the encryptor may output the message in the clear;
* otherwise BGG+ simulation gives `A_φ = B R_φ^{(0)}` with
  `R_φ^{(0)} = evalSim(φ, A_j, 0, R T_W[j])` short, so `[B | A_φ − G]` has the `−G` trapdoor
  `R_φ^{(0)}`. The encryptor samples the leaf key with one try of box rejection using it.

Any fixed public point `x₀` can replace `0`. The trapdoor `T` of the succinct-LWE instance does not
help directly: it gives trapdoors of `[B | W_i]`, and LWE samples `sᵀ[B | W_i] + e` are then
insecure (`sᵀ G` is recovered with `T`). That is why the leaf matrix stays `[B | A_φ − G]`.

## Proved (all `ACCEPTED` locally, self-contained proofs)

* `leafView_close` (any finite commutative ring `K`). The setup is any kernel
  `S : B ↦ (W, T)`. A public check `good(T)` decides whether a key is sampled; otherwise the key is
  `⊥`. The hypotheses are the block identity `B T_B[i,j] + W_i T_W[j] = δ_ij G` and box coverage on
  the good outputs of `S`. Under them, the **real view** `(B, (W, T), A = B R, key)` (attribute
  `0`, key with `R_φ^{(0)}`) and the **simulated view** `(B, (W, T), A = Σ w_i W_i + B R, key)`
  (attribute `w` with `φ(w) = 0`, key with `R_φ^{(w)}` from `R T_W[j] − Σ_i w_i T_B[i,j]`) are
  within `2 · m_W √(|K|^n / 2^m) / 2`. Proof: the key law of one box-rejection try does not depend
  on the trapdoor (`boxSample_eq`). Both views are therefore experiments that read only `B` and the
  hashes `B R`. The leftover hash lemma (`closeTo_binaryHash_bind`) makes `B R` uniform in both.
  After that, `A = c(W) + U` is uniform for any shift `c(W)`, so the two ideal experiments are
  **equal**.
* `leafCover_zmod`: over `ℤ_q`, a simulation trapdoor with entries at most `errBound k E φ` keeps
  `ball s` inside the big box of `Bb` bits when `s + k · errBound k E φ ≤ 2^{Bb−1} − 1`. Here `E`
  bounds the input-trapdoor entries.
* `leafView_close_zmod`: the end-to-end leaf statement over `ℤ_q` (the ring of `Def_SuccinctLWE`).
  It assumes that `good(T)` bounds the entries of `T_B`, `T_W` by `E_T`, that the attribute `w` is
  binary, that `φ(0) = φ(w) = 0`, and that `s + k · errBound k ((m_W + ℓ) E_T) φ ≤ 2^{Bb−1} − 1`.
  The two views are then within `m_W √(q^n / 2^m)`.

This **closes gap (2)**, the attribute-encoding hop. The leftover hash lemma is applied with the
key, `W` and `T` all in the view. That works because the key law depends on `R` only through
`B R`.

## Gap (3) is no longer a security gap

`good(T)` is a public check on `T`. Real and simulated views both output `⊥` when it fails, so the
theorem holds for **every** setup kernel `S`, Gaussian `T` included, with no tail bound. The tail
bound `Pr[¬good(T)] ≤ ε` is still needed, but only quantitatively:

* for correctness, if the encryptor outputs `⊥` when the check fails;
* or for the tightness of the reduction, if the encryptor resamples, because the reduction then
  aborts on challenger instances with `¬good(T)`.

`SigabaNeoStd`'s `cosetGauss_tail` gives the per-column bound `Pr[‖x‖ ≥ σ √M] ≤ 3·2^{−M}` once
`dualMassE([I_ℓ ⊗ B | W], σ) ≤ 1/2`. What is missing is that smoothness for **most** `(B, W)`
(`card_bad_le` covers uniform matrices, not the block form) and the union bound over the `ℓ n k`
columns.

## What remains

1. **(1b) The encryptor's own setup.** `Def_WE_CircuitSAT` has no common reference string, so the
   encryptor must sample `(B, W, T)` itself, close to the challenger's law. Proposed route, with no
   trapdoor for `B`: `B` uniform; `W = [W̄ | H − W̄ R_W]` with an MP12 gadget trapdoor (`H` the
   `ℓn`-row gadget). Each column of `T` is the flooding sample `y + [0; x_W(t − M y)]` with
   `y ← D_{Z^{ℓm+m}, σ}`, `M = [I_ℓ ⊗ B | W]` and `x_W` the short `W`-preimage. The needed lemmas:
   * (a) the generalization of `SigabaNeoStd`'s `Trapdoor.Family.colLaw_close` from `Bmat` to any
     `M` with a short preimage map `d` (`M d(v) = v`, `|d(v)_j| ≤ b`). The expected conditions are
     `τ ≥ 1`, `τ√m + b ≤ τ m` and `dualMassE M τ ≤ 1/2`, with the same error
     `2θ + 6 m 4^{−m} + 3·2^m 4^{−m²}` and `θ = π m (b² + 2 τ m b)/τ²`. The proof there uses only
     these facts;
   * (b) smoothness of `Λ^⊥([I ⊗ B | W])` for most `(B, W)` (also needed for gap 3);
   * (c) `W ≈` uniform (leftover hash, as in `closeTo_genB`) and independence of the columns
     (`closeTo_sampleOptList`).

   The flooding forces `σ ≳ m^{1.5} b 2^κ`. `Def_SuccinctLWE`'s `H` only bounds `σ` from below, so
   the claimed strength is unchanged. The larger `E_T ≈ σ √M` enters the leaf coverage condition
   and costs about `κ + O(log)` extra bits of `q`.
2. **Instantiation with `Def_SuccinctLWE`'s law.** `S B := (W ← uniform, T ← trapdoorLaw p B W)`,
   with `T_B`, `T_W` the blocks of `T` reduced mod `q` and `good(T) := T ≠ none ∧` (entries
   `≤ E_T`). The block identity holds on the support because preimage outputs lie in their cosets.
   This plumbing is not formalized. The theorem also takes a `ℤ_q` gadget `Γ` with
   decompositions of entries at most `1` as a hypothesis.
3. **Multi-column keys, parameters, and the computational half of (C1)**: unchanged from
   `pq-we-leaf-key-exact-simulation`, items 1, 5 and 6. Over `ℤ_q` the abort probability of the box
   sampler (the analogue of `leafKey_abort_le`) only matters for correctness, since the laws agree
   including aborts.
4. The internal-node step (C2) of the tree candidate is untouched. It is still FE-hard
   (`pq-we-tree-candidate-crux`), so this leaf lemma is a reusable piece, not a WE scheme.
