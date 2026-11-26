---
title: Evaluation collisions for witness-oblivious target cancellation - a kernel-collision candidate, its attack, and the rank-one decomposed-LWE variant
refs: [definition:WE_CircuitSAT, definition:DecomposedLWE, note:pq-we-evaluation-oracle-crux, note:pq-we-rank-gap-lattice-barriers]
tags: [witness-encryption, candidate, attack, barrier]
---
`pq-we-evaluation-oracle-crux` reduces lattice WE to giving, next to the BGG+ encoding
`c_1 = sᵀ(A − φ ⊗ G) + e`, a second representation of `w ↦ sᵀ A_{U_w}`. Its "data-only" form is a
second set of LWE samples, on *different* matrices `A'`, whose evaluations agree with those of `A`:
an **evaluation collision**. This note records one explicit candidate of that kind, an attack on
it, and the general reason such collisions fail. It also covers the same idea in the
rank-one structure of decomposed LWE. Informal arguments, no Lean proofs.

## Candidate: kernel collision on a switch wire

Extend the attribute with a switch bit `b` and evaluate `f_w(φ, b) = φ(w) ∧ b` as a BGG+
multiplication with `b` as the right operand, so that `A_{f_w} = −A_{U_w} G^{-1}(A_b)` (any short
preimage of `A_b` may replace `G^{-1}(A_b)`). Publish the φ-encodings and **two** encodings of
the switch wire:

* `k_b = sᵀ(A_b − G) + e` (value `1` on matrix `A_b`);
* `k'_b = sᵀ(A_b − G Δ) + e'`, read as value `0` on the matrix `A'_b = A_b − G Δ`, whose short
  preimage is `X' = G^{-1}(A_b) − Δ`.

Then `A'_{f_w} = A_{f_w} + A_{U_w} Δ`. If `A_{U_w} Δ = 0` for every `w`, the two evaluations give
`sᵀ(A_{f_w} − φ(w) G)` and `sᵀ A_{f_w}`, and their difference is `φ(w) · sᵀ G`: correct
decryption with no per-witness key. The encryptor can arrange `A_{U_w} Δ = 0` for all `w` without
knowing any witness by ending `U_w` with a multiplication by a constant-`1` wire of matrix `C`, so
that `A_{U_w} = Y_w P` with the fixed factor `P = G^{-1}(C)`. It then picks `C` such that `P` has a
short kernel vector and takes `Δ` with `P Δ = 0`.

### Attacks

1. **Low-rank `Δ`.** A short kernel vector of a binary `P` (e.g. two equal columns of `C`) gives
   a low-rank `Δ`. Then `k'_b − k_b = sᵀ G (I − Δ) + noise` equals `sᵀ G` on every column that
   `Δ` does not touch, and gadget decoding returns `s`.
2. **Structural collisions are reachable by any circuit (general).** Even for a `Δ` that avoids
   attack 1, the identity `A_g Δ = 0` holds for **every** circuit `g` whose last gate is the
   multiplication by the constant wire `C`. It depends on the evaluated *matrix*, i.e. on the
   circuit's structure, never on the value `g(φ)`. The adversary takes `g = (x_1 ∨ ¬x_1) ∧ 1_C`,
   which has value `1`, runs the decryption with `g` in place of `U_w`, and obtains `sᵀ G`.

## Why evaluation collisions fail in general

The decryptor needs two evaluation paths with **equal matrices** and values differing by `φ(w)`.
With BGG+ (and its succinct/decomposed variants) the matrices are computed from public data by
`EvalPK`, so:

* a collision that holds **for structural reasons** (a shared factor, a kernel, a factorization
  such as `A_i B_j`) is a property of circuit shapes. The adversary can realize the same shape with
  a constant-`1` circuit (in the candidate above it suffices to end with the same last gate;
  in general one pads a constant-`1` circuit to the required shape), and decrypts without a
  witness. Whether every structural collision can be reached this way is not proved; it holds for
  every collision mechanism found so far;
* a collision that is **not structural** has to hold simultaneously for the `2^128` pseudorandom
  matrices `A_{U_w}` (they involve `G^{-1}` of `A`-dependent matrices). There is no known
  mechanism for that, and generically the common kernel of `2^128` such matrices is `{0}`
  (once their row spaces span `Z_q^m`).

So the value gate `φ(w)` cannot be moved into the matrices. It must stay in the encoded values
(`c_1`), and the second path must hide its own matrices. That is an obfuscation again
(`pq-we-evaluation-oracle-crux`).

## The rank-one decomposed-LWE variant

Decomposed LWE (`Def_DecomposedLWE`) gives `y_{ij} = sᵀ(A_i B_j + δ_{ij} G) + e_{ij}` with public
`A_i` (uniform) and `B_j` (short). For any short integer `N`,
`Σ N_{ij} y_{ij} = sᵀ(Σ N_{ij} A_i B_j) + tr(N) sᵀ G + small`. For a rank-one `N = u vᵀ` the
matrix factors as `A_u B_v` (`A_u = Σ u_i A_i`, `B_v = Σ v_j B_j` short), which matches the
rank-one certificate `Σ a_k M_k = u vᵀ` of Hair–Sahai. Decryption would need a second path to
`sᵀ A_u B_v`, i.e. access to `sᵀ A_u` (then multiply by the public short `B_v`).

**Attack (linear closure).** The decryptor's `u` depends on the unknown witness, so the access
must work for every `u ∈ {0,1}^t` the scheme cannot exclude, in particular `u = e_i`. That gives
`sᵀ A_i B_j + small` for all `i, j`, and `y_{ii} − sᵀ A_i B_i = sᵀ G + small`. More generally,
noisy-linear encodings are closed under short linear combinations, and rank-one matrices with
`{0,1}` factors span all matrices through short combinations, so rank cannot gate access. The
matrices `A_u B_v` are a structural collision in the sense above. Unlike Barrier 1 of
`pq-we-rank-gap-lattice-barriers`, this attack is explicit and needs no linear-only assumption: the
MinRank structure adds nothing a lattice encoding can enforce.

## Verdict

Dead: the kernel-collision candidate (attacks 1 and 2) and rank-one access in decomposed LWE.
A lattice WE needs a second representation of `w ↦ sᵀ A_{U_w}` whose matrices are hidden. All
known ways to hide them are obfuscation (iO), evasive-type assumptions (GGH15 with a statement-
dependent hint), or ideal models.
