---
title: Barriers for a lattice analogue of rank-gap witness encryption
refs: [definition:WE, definition:WE_CircuitSAT]
tags: [witness-encryption, strategy, barrier]
---
Direction 1 of the post-quantum WE survey asks for a standard-model, post-quantum replacement for
the generic group in Hair–Sahai's rank-gap witness encryption (arXiv 2609.18275, §3). This note
records why the obvious replacements fail, so later attempts can start past these points. These
are informal (asymptotic) arguments, not Lean proofs.

## The structure to preserve

The ciphertext is `([s_i], [sᵀ M_j r])` (β = 0) or `([s_i], [t_j])` (β = 1), where `r ← {1..m}^m`.
A witness gives `a` and `u` with `Σ a_j M_j = u vᵀ`, `v ∈ {0,1}^m`. Decryption is one linear test
with a short search: `Σ a_j Y_j = c · Σ u_i X_i` for some `c = vᵀ r ≤ m²`. The security proof uses
only that every test of the adversary is linear: `sᵀ(α + N r) = 0` with `rank N ≥ R`, which
succeeds with probability at most `m^{-R}`. That counting step is assumption-free and proved in
the DAG (`AdvancedEncryption.WE.RankGap.card_solutions_le`).

## Barrier 1: the proof is a linear-only argument

The security argument needs the adversary to be restricted to linear tests on the encodings. In
the standard model, that restriction is exactly a *linear-only encoding* assumption (Bitansky,
Chiesa, Ishai, Ostrovsky, Paneth). It is a knowledge-type assumption and is not falsifiable. Any
construction whose proof goes "every efficient test is (close to) linear, then rank gap" therefore
needs a different, falsifiable reason for the restriction.

## Barrier 2: statistical security cannot work for NP-complete statements

Write the encodings as noisy linear measurements `y = W z + e (mod q)`. Here `W` is public and
depends on the statement, and decryption uses a short witness-derived `λ` with `λᵀ W = 0 (mod q)`,
so that `λᵀ y = λᵀ e` is small.

* If the dual lattice `{λ : λᵀ W ≡ 0}` has no vector shorter than about `√N / σ`, then `σ` exceeds
  the smoothing parameter of the primal lattice. In that case `y` is statistically close to
  uniform and security is statistical.
* But statistical WE for a language `L` puts `L` in SZK. The map `φ ↦ (Enc(φ,0), Enc(φ,1))` reduces
  `L` to Statistical Difference (Sahai–Vadhan): the distance is close to 1 when `φ ∈ L` (by
  correctness) and close to 0 when `φ ∉ L`. So `SZK ⊆ AM ∩ coAM` would give `NP ⊆ coAM`, and the
  polynomial hierarchy would collapse.
* Consequently the NO case must leave dual vectors of intermediate length, between `√N/σ` and
  `q/σ`, and security must be computational.

## Barrier 3: computational security on a statement-dependent matrix is not allowed

In that computational regime, the natural assumption is "`(W_φ, W_φ z + e)` is pseudorandom for
every `φ ∉ L`". This is statement-dependent and hence excluded. Making it statement-independent
requires `W_φ = f_φ(A)` for a uniformly random `A`, with a reduction from plain LWE on `A`.
Lattice homomorphic evaluation (GSW, BGG+) produces short dual vectors of `Eval(A, C)` only
relative to `[A − x ⊗ G]`. That means the party building the ciphertext must embed the input `x`,
which is the witness here. The encryptor of WE does not know the witness, so this route gives ABE
or WE for P (as with decomposed LWE, ePrint 2025/339 §7), not WE for NP.

## Barrier 4: LPN-type encodings

LPN or code-based encodings of `sᵀ M_j r` are linear, but an adversary is not limited to linear
tests (for example, it can run information-set decoding on structured codes). Barrier 1 applies
unchanged.

## What a construction must therefore contain

1. A falsifiable, statement-independent assumption that is used to hide *quadratic* data
   `sᵀ M_j r`. A bilinear structure, at least computationally, seems necessary, since the decryption
   test pairs `s` with `r`.
2. An encryptor that needs no witness: the witness enters only through the linear-test
   coefficients `(a, u, c)` at decryption time.
3. A reduction that turns "no low-rank matrix in `S`" into indistinguishability, with no
   linear-only step.

The open question this leaves for the DAG: is there a lattice encoding of `(s, sᵀ M_j r)` that
(i) supports the decryption test using a short combination only, and (ii) is pseudorandom under a
fixed lattice assumption whenever `S` has no low-rank element? Candidate encodings and their
attacks will be recorded as further notes.
