---
title: BGG+ witness encryption is LWE-secure in one hop given an evaluation oracle - the whole difficulty is obfuscating one statement-independent function
refs: [definition:WE, definition:WE_CircuitSAT, note:pq-we-hybrid-count-barrier, note:pq-we-function-hiding-crux, note:pq-we-decryptor-attribute-dead-end]
tags: [witness-encryption, barrier, strategy]
---
This note pins down the "witness-oblivious target cancellation" problem
(`pq-we-decryptor-attribute-dead-end`) as one object: an obfuscation of a single,
statement-independent lattice function. It is an informal argument (no Lean proof yet).

## Notation

BGG+ attribute encodings: for an attribute `x ∈ {0,1}^L`, uniform `A = [A_1 | … | A_L]` and
`c = sᵀ(A − x ⊗ G) + e`. For a circuit `f` there are `A_f = EvalPK(f, A)` and a short
`H_{f,x}` (computable from `A, f, x`) with `(A − x ⊗ G) H_{f,x} = A_f − f(x) G`.
Take `x = φ` (the description of the NAND circuit, which the encryptor knows) and the universal
circuit `U_w(x) = x(w)` with `w` hard-wired.

## The scheme in the oracle model

* `Enc(φ, μ)`: `s ← Z_q^n`, `A`, `u` uniform; `c_1 = sᵀ(A − φ ⊗ G) + e_1`,
  `c_2 = sᵀ u + e_2 + μ⌊q/2⌋`. The decryptor also gets oracle access to
  `F_{s,A}(w) = ⌊sᵀ A_{U_w}⌉_p`.
* `Dec(φ, w)`: `F_{s,A}(w) − ⌊c_1 H_{U_w,φ}⌉_p = ⌊φ(w) · sᵀ G⌉_p ± 1`. For `φ(w) = 1` this gives `s`
  (gadget decoding, `q` a power of two), then `μ` from `c_2`.

**Security on a false `φ`, one computational hop.** For every `w`, `φ(w) = 0`, so
`c_1 H_{U_w,φ} = sᵀ A_{U_w} + e_1 H_{U_w,φ}` and the oracle is answered as `⌊c_1 H_{U_w,φ}⌉_p`.
This is correct unless `sᵀ A_{U_w}` lies within `‖e_1‖ β` of a rounding boundary (statistical
hop; for exact agreement on all `2^128` inputs take `q/p ≥ 2^{128+κ} β ‖e_1‖`). The oracle is now
a public function of `c_1`, and `(c_1, c_2)` are LWE samples on the uniform matrix
`[A − φ ⊗ G | u]` (plain LWE; no planting, no trapdoor). No witness-indexed hybrid appears,
which does not contradict `pq-we-hybrid-count-barrier`, since the oracle is not part of the
ciphertext.

The oracle `F_{s,A}` is the PRF of Brakerski–Vaikuntanathan's constrained key-homomorphic PRF
(TCC 2015), and `c_1` is its constrained key for the constraint `φ`. So the ciphertext is
"a constrained key for `φ` plus the master function", and on a false statement the constrained
key already computes the master function everywhere.

## Consequences

1. **The missing object is statement-independent.** A WE ciphertext is
   `(c_1, c_2, O)` where `O` is any efficient representation of `F_{s,A}`, a function of `(s, A)`
   alone, such that
   `(c_1, c_2, O) ≈ (c_1, c_2, O')`, with `O'` a representation of
   `w ↦ ⌊c_1 H_{U_w,φ}⌉_p` built from `c_1` (for false `φ` the two functions are equal).
   With iO this holds (this is the folklore WE from iO plus a constrained PRF). Without iO it is
   the target-cancellation problem, now with an exact target. By
   `pq-we-hybrid-count-barrier`, the step `O ≈ O'` has no polynomial-hop proof from
   statement-independent assumptions (everything else in the proof is one LWE hop), so its proof
   must walk over `w`.
2. **The difficulty is not in the hybrid structure.** Positional/threshold variants
   (`pq-we-function-hiding-crux`) need the same object already for correctness at position `0`:
   a valid witness must decrypt the real ciphertext, so the real ciphertext must contain some `O`.
   Changing the proof (tree, positional, data-only hops) cannot remove this requirement; only a
   different `O` can.
3. **What a "data-only" `O` must look like.** If `O` is a list of LWE-type samples `sᵀ X + e` with
   public `X` and public short `H'_w` with `X H'_w = A_{U_w}`, the step `O ≈ O'` is free when both
   are generated from the same samples. The two obvious choices fail:
   * `X = A` (the encoding of an attribute `φ_0` with `φ_0(w) = 0` for all `w`): `c_1` and `O`
     share the matrix `A` with different attribute values, and `O − c_1 = sᵀ(φ ⊗ G) + small`
     gives `s`.
   * `X` with a public trapdoor: every target, including `G`, is reachable, and `s` leaks.
   Any other choice needs two different matrix tuples whose evaluations agree on every `U_w`.
   Such "evaluation collisions" are analysed in `pq-we-matrix-collision-barrier`.

## Status

This is a reformulation, not a construction. It is useful because it isolates a single,
statement-independent object (`F_{s,A}` with `A` public) whose secure representation would give
WE from plain LWE with a one-hop proof plus one statistical step, and it shows that all
witness-indexed hybrid designs still have to produce this object.
