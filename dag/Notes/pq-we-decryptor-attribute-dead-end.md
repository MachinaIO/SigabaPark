---
title: Dead end - letting the decryptor choose the BGG+ attribute through the succinct-LWE trapdoor
refs: [definition:SuccinctLWE, definition:WE_CircuitSAT]
tags: [witness-encryption, dead-end]
---
This records an attempt to remove the witness-dependent key at the leaf of the witness-tree
candidate, so later attempts can skip it.

## The attempt

With the ℓ-succinct LWE trapdoor `[I_ℓ ⊗ B | W] T = I_ℓ ⊗ G` public, a decryptor holding `w` can
form attribute keys `A_j(w) = (Σ_i w_i W_i + B R) T_W[j] = B R_j(w) + w_j G` for *any* `w` it
chooses (Wee's identity, `AdvancedEncryption.WE.Wee.wee_identity`). Here `R_j(w)` is short and
computable when `R` is public. The idea was to publish only `sᵀB + e` and let the decryptor
build BGG+ encodings `sᵀ(A_j(w) − w_j G) = sᵀ B R_j(w)` of its own witness, so that the encryptor
never needs `w`.

## Why it fails

BGG+ evaluation of `φ` on these encodings gives `sᵀ(A_φ(w) − φ(w) G) + e_φ`. By the simulation
relation this is `sᵀ B R_φ(w) + e_φ`, a value the decryptor could compute anyway, so nothing turns
on when `φ(w) = 1`. Opening a message needs `sᵀ A_φ(w)` (or `sᵀ G`) separately. `A_φ(w)` depends
non-linearly on `w` (through `G^{-1}` in each NAND step), so `sᵀ A_φ(w)` is not a fixed linear
combination of published samples. The encryptor would have to supply it for every `w`. This is
again the *witness-oblivious target cancellation* problem of `pq-we-tree-candidate-crux` and
`pq-we-function-hiding-crux`: the decryptor needs a target-dependent term that the encryptor can
only provide through a key whose function depends on `w` (ABE key, FE) or through a
statement-dependent hint (evasive LWE).

## Lesson

Public trapdoors such as succinct LWE's let the *decryptor* move attributes into BGG+ form for
free, but they do not supply the one non-linear quantity `sᵀ A_φ(w)` that decryption needs. Any
fix must say where that quantity comes from, and must do so without a per-`w` key.
