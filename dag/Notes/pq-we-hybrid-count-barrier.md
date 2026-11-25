---
title: WE from statement-independent assumptions needs exponentially many hybrids (and what that means concretely)
refs: [definition:WE, definition:WE_CircuitSAT]
tags: [witness-encryption, strategy, barrier]
---
This note records a structural barrier that shapes every Design-AI attempt at the post-quantum WE
problem (`Def_WE_CircuitSAT`). The argument came from a brainstorm with a second AI model and was
checked by the submitting agent. It is an informal, asymptotic complexity argument, not a Lean
proof.

## The barrier (poly-hybrid proofs imply L ∈ SZK)

Take a WE scheme for a language `L` with a security proof of the usual shape: efficiently
samplable distributions `H_0 = Enc(φ, 0), H_1, …, H_T = Enc(φ, 1)` with `T = poly(|φ|)`. Each hop
`H_i → H_{i+1}` is one of two kinds:

* **statistical**: negligible statistical distance whenever `φ ∉ L`; or
* **computational**: indistinguishable under an assumption whose instances do not depend on `φ`.
  Such an assumption holds for *every* `φ`, including `φ ∈ L`.

Fix `φ ∈ L` with a witness `w`. The decryptor `Dec(φ, w, ·)` is an efficient distinguisher with
advantage `≈ 1` between `H_0` and `H_T` (correctness). Its advantage on every computational hop is
negligible, so the statistical hops must carry total distance `≥ 1 − negl`. When `φ ∉ L`, that
total is `negl` by assumption.

Pick a random statistical hop `i` and output the pair of distributions `(i, H_i)` and
`(i, H_{i+1})`. This maps `L` to Statistical Difference with gap `1/T` versus `negl`, which
polarizes (Sahai–Vadhan). Hence `L ∈ SZK ⊆ AM ∩ coAM`. For `L` NP-complete, the polynomial
hierarchy collapses.

The same argument covers the purely statistical case: statistical WE for `L` gives `L ∈ SZK`
directly.

## Consequences

1. **Statement-independent assumptions plus a polynomial-loss proof cannot give WE for NP**
   (unless PH collapses), whatever the algebra: lattices, codes or isogenies. This is the abstract
   form of the barriers in `pq-we-rank-gap-lattice-barriers`. Hair–Sahai escape it through the
   generic group model. Evasive-LWE and statement-dependent candidates escape it by making the
   assumption depend on `φ`. iO-based WE escapes it through an exponential number of hybrids
   together with sub-exponential hardness.
2. **The escape left within our constraints is an exponential number of hybrids**, roughly one per
   candidate witness (as in positional WE, Gentry–Lewko–Waters, CRYPTO 2014). Each hop uses only
   the *local* fact that one candidate `w` fails, `φ(w) = 0`, together with a statement-independent
   assumption.
3. **In the concrete setting of Sigaba Neo this is not fatal.** `Def_WE_CircuitSAT` has 128-bit
   witnesses, so a proof with about `2^128` hops, each costing `cost/adv² ≥ 2^k` under its premise,
   gives false-statement security with about `k − 2·128` bits (advantages add across hops and
   `Problem.gain` is squared). Premises of roughly `128 + 2·128 = 384` bits then suffice. Plain
   LWE / succinct LWE at such strengths only needs larger parameters.

## Design requirements this imposes

* The scheme must admit a hybrid sequence indexed by the witness space `{0,1}^128` (or a
  tree / positional structure over it). Each hop switches the contribution of one candidate
  witness (or one subtree) using a statement-independent assumption, and the step is justified by
  the local evaluation `φ(w) = 0`.
* Decryption with a valid `w` must be efficient, so the ciphertext cannot contain a separate
  component for each candidate witness. The per-witness structure must be *implicit*: a
  homomorphic evaluation over `w` that the decryptor performs. This is where lattice tools enter
  (BGG+ attribute encodings with the circuit `U_w(φ) = φ(w)`; succinct LWE's Gaussian preimages
  `[I_ℓ ⊗ B | W]^{-1}(I_ℓ ⊗ G)` as public "trapdoors for every block").
* The remaining obstacle (from the same brainstorm): in BGG+ the decryptor obtains
  `sᵀ(A_{U_w} − φ(w)·G) + e'`, but `A_{U_w}` depends on the unknown `w`. Cancelling `sᵀ A_{U_w}`
  without a trapdoor is the witness-oblivious target-cancellation problem. A construction must
  solve it, for example by making the cancellation term itself the output of a positional or
  tree-structured encoding whose hybrid argument walks over `w`.

Next Design-AI step: formalize the hybrid-count accounting as a Lean lemma (a generic "sum of `2^n`
hops" bound in the `Problem.decision` / `gain` vocabulary), so that a later construction can plug
in its per-witness hop.
