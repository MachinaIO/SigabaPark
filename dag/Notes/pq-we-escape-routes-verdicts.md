---
title: Four proposed escapes from the WE barriers - anti-concentration, lattice subgroups, lockable obfuscation, exponential-time reductions - and why each fails
refs: [definition:WE_CircuitSAT, note:pq-we-hybrid-count-barrier, note:pq-we-rank-gap-lattice-barriers, note:pq-we-function-hiding-crux, note:pq-we-evaluation-oracle-crux]
tags: [witness-encryption, dead-end, barrier]
---
These are short verdicts from the Design-AI search for witness-indexed WE proofs whose hops change
only ciphertext data. Each was proposed as a way past the recorded barriers
(`pq-we-hybrid-count-barrier`, `pq-we-function-hiding-crux`, `pq-we-evaluation-oracle-crux`).
All arguments are informal.

## 1. Jutla's anti-concentration condition (ePrint 2026/2995) in place of rank

Jutla keeps Hair–Sahai's ciphertext and replaces "every nonzero `M` in the instance space has
rank `≥ R`" by "every nonzero `M` that does not allow witness extraction has small collision
probability `κ_B(M) ≤ B^{-(t+1)}` for `M r`" (§8, Theorem 8.1; §9 derives the same from linear
affine-source extractors). The proof is a symbolic-label generic-group argument. A union bound
runs over the adversary's pairs of formal expressions, and the new condition only supplies the
small-ball estimate for each one.

**Verdict: no data-only hops.** The quantity bounded is per *test* (a matrix `M_γ` the adversary
forms), not per *candidate witness*. On a false instance, the candidate witnesses do not
correspond to any element of the instance space `S_x`. There is no local fact `φ(w) = 0` that
changes the encoding at one position, so no witness-indexed hybrid can be read off. In the
standard model the restriction to linear tests is still Barrier 1 of
`pq-we-rank-gap-lattice-barriers` (linear-only encodings). Replacing rank by min-entropy weakens
the combinatorial premise (and gives smaller ciphertexts) but does not touch that barrier.

## 2. Gentry–Lewko–Waters positional WE translated to lattices

GLW's hops are data-only: the position is held in subgroup components of composite-order
multilinear encodings, and subgroup-elimination steps move it.

* **CRT subgroups fail at once.** With `q = q_1 q_2` and noise `e` that is small (or `q_2 · small`),
  the component of `sᵀA + e` modulo `q_1` reveals whether `s ≡ 0 (mod q_1)`: subgroup decision is
  easy for LWE.
* **Secret-subspace "subgroups"** (`s ∈ span(V)` versus uniform) are LWE-hard, but GLW also needs
  degree-`n` products of encodings along the witness. The lattice tool for that is a GGH15 chain.
  The chains provable from LWE (read-once, fresh LWE secrets per level, Chen–Vaikuntanathan–Wee
  2018) are pseudorandom and carry no statement gate. Gating needs a BGG+ leaf whose cancellation
  term is the object of `pq-we-evaluation-oracle-crux`, and with it come the evasive-LWE
  candidates (Tsabary 2022, Vaikuntanathan–Wee–Wichs 2022).

## 3. Lockable obfuscation (Goyal–Koppula–Waters, Wichs–Zirdelis 2017) per witness

Lockable obfuscation is a GGH15-based obfuscation that is *provable* from LWE because the lock `α`
is uniform and independent of the program: the program never accepts. A false statement also never
accepts, which suggests obfuscating `w ↦ [φ(w) = 1]`. But the lock then has no entropy. Making it
random requires the program to output `α` on witnesses, so the program depends on `α`, and the
security theorem no longer applies. With FHE, `P(w) = Dec_sk(Eval(f_w, Enc(α)))` contains both
`sk` and `Enc(α)`. Turning φ's evasiveness into lock entropy is exactly null-iO. **Verdict: dead**,
and in substance an iO route.

## 4. Exponential-time reductions (a way around the SZK argument?)

`pq-we-hybrid-count-barrier` assumes efficiently samplable hybrids. With κ = 128, a hop whose
reduction runs in time `2^128 · poly` is affordable against premises of about 384 bits. Such a
reduction can, for instance, compute the whole truth table of
`w ↦ ⌊c_1 H_{U_w,φ}⌉_p = F_{s,A}(w)` from `c_1` alone (the notation of
`pq-we-evaluation-oracle-crux`). It could then sample the ciphertext's representation `O` of
`F_{s,A}` from the truth table, without `s`, *if* the distribution of `O` depended only on the
function `O` represents.

**Verdict: does not help.** Two cases:

* `O` is a function of polynomially many table entries (for example, a list of noisy values
  `F(w')` on a fixed set `S`). Then `O` is also computable in *polynomial* time from `c_1`
  on false statements, since every `F(w')` is. The proof then has polynomially many efficient
  hops, so by the SZK argument the scheme cannot be correct on true statements.
* `O = g(s)` depends on the table only through `s` (the table determines `s`, so every
  efficient `O` is formally a function of the table). Then sampling `O` from the
  truth table means recovering `s` from `2^128` rounded LWE samples. That is far beyond `2^128`
  work at secure dimensions (BKW-type attacks need `2^{Ω(n / log n)}`). Making the representation
  canonical (for example, the lexicographically first circuit, or the shortest preimage for
  keys) costs more than `2^128` and is not what an efficient encryptor outputs.

The two cases are not exhaustive. A representation that depends on exponentially many table
entries yet is computable from the table in time `2^128` without recovering `s` would escape. No
such representation of a pseudorandom function is known, and finding one is a precise open
question. Short of that, exponential-time reductions are interchangeable with witness-indexed hybrids, as the
hybrid-chain accounting already says, and they do not create a new escape.

## Summary

None of the four directions yields hops that change only ciphertext data. In each case the step
that fails is the same: a representation of `w ↦ sᵀ A_{U_w}` (or of an equivalent gate) whose
indistinguishability from the planted representation is not a function-hiding statement.
