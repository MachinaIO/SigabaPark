---
title: WE in the concrete regime (n = 128) - fine-grained, exponential-time and meet-in-the-middle routes, and an evaluation-only lower bound
refs: [definition:WE, definition:WE_CircuitSAT, note:we-circuitsat-bruteforce-explicit-cost, note:pq-we-hybrid-count-barrier, theorem:AdvancedEncryption.WE.Hybrid.stat_hops_carry]
tags: [witness-encryption, strategy, barrier, lower-bound, fine-grained]
---
`WE_CircuitSAT` is concrete: `n = 128` input bits, `s = 2^12` NAND gates, `λ = κ = 128`,
security `cost(A) / Adv² ≥ 2^128` for every explicit adversary (which may depend on `φ`), and the
submission is ranked by `N = time(Enc) + time(Dec) + descLen`. The assumption-free baseline has
`N ≈ 2^188` (note `we-circuitsat-bruteforce-explicit-cost`), with an intrinsic count of
`2^128 · 2^12 = 2^140` gate evaluations and a known route to about `2^165` on the tape model.

The question here: since asymptotic barriers (note `pq-we-hybrid-count-barrier`) do not apply
literally at fixed `n`, can honest algorithms that run in exponential but sub-brute-force time
(`2^60` to `2^150`) beat the baseline using fine-grained gaps? This note answers **no for every
route that uses the circuit only through evaluations**, with a proved concrete bound, and isolates
what a non-black-box route would need.

## 1. The evaluation-only lower bound (proved)

**Model.** Call a scheme *evaluation-only* if `Enc` and `Dec` use the statement `φ` only as an
oracle `x ↦ φ(x)` (plus any statement-independent computation: PRGs, hashes, LWE samples,
tables, puzzles). Meet-in-the-middle tables, Merkle-style puzzles, hashing of candidate witnesses,
time-lock-style padding and exhaustive search over a reduced space are all of this kind.

**Argument.** Let `f_0 ≡ 0` (a false statement) and `f_w` the point predicate true only at `w`.
Runs of `Enc^{f_0}(β)` and `Enc^{f_w}(β)` coincide until `Enc` queries `w`, so their ciphertext
laws are within `p_β(w) := Pr[Enc^{f_0}(β) queries w]` in statistical distance, and
`Σ_w p_β(w) ≤ q` (the expected number of distinct queries). For each `w` let `A_w` be
`Dec(·, w, ct)` with `w` hard-wired and its oracle simulated as `x ↦ [x = w]`. Correctness on
`(f_w, w)` gives `A_w` advantage `≥ 1 − 2·2^{-κ}` on `Enc^{f_w}`. Averaging gives a `w` with
`p_0(w) + p_1(w) ≤ 2q / 2^n`, and for that `w` the adversary `A_w` against the **false** statement
`f_0` has advantage `≥ 1 − 2^{1−κ} − 2q/2^n`.

Two DAG theorems state this with complete proofs (in the `SigabaNeo.Machine` / `Problem.decision`
vocabulary, with the coupling and correctness facts as hypotheses):

* `AdvancedEncryption.WE.EvalOnly.query_lower_bound`: in general, some `A_w` costs at least
  `2^k (1 − ε − 2q/|W|)²`.
* `AdvancedEncryption.WE.EvalOnly.query_lower_bound_128`: at `|W| = 2^128`, `ε ≤ 2^{-127}`,
  `k = 128`: if `q ≤ 2^125` then some `A_w` costs at least `2^127`.

**Concrete consequence.** `cost(A_w) ≤ time(Dec)·O(n) + descLen(Dec) + O(n)` (each simulated query
is a 128-bit comparison). So an evaluation-only scheme has either `≥ 2^125` encryptor queries or
`time(Dec) ≳ 2^127 / O(128) ≈ 2^120`. Hence

    N(evaluation-only) ≳ 2^120,   while brute force is ≈ 2^140 intrinsically.

The *exponent* cannot be improved by any evaluation-only trick; at most the per-evaluation factor
`s = 2^12` and the tape-model overheads (the `2^188 → 2^165 → 2^140` path) can be removed. This is
the relativized form of the WE barrier, made concrete; the concrete regime does not rescue it,
because the bound is already stated at `n = 128`.

## 2. The routes, one by one

**(1) Split the witness, precompute over halves (meet in the middle).** Write `x = (x_1, x_2)`
with `|x_1| = a`. Any scheme that enumerates `x_1` and, for each, emits something a holder of
`x_2` can open is a WE for the residual circuit `φ(x_1, ·)` (`n − a` inputs, still `2^12` gates).
Costs multiply: `N(n) ≥ 2^a · N_base(n − a)`; the false-statement proof is a hybrid over the `2^a`
components, so each needs `cost/adv² ≥ 2^{128 + 2a}`. If the residual WE is brute force,
`N = 2^a · 2^{n−a} · s = 2^140`: no gain. The tempting cheap residual - Yao-garble `φ(x_1, ·)` and
publish *both* labels of every `x_2` wire, hiding `β` under the output-1 label - is broken: an
evaluator mixes labels from different evaluations at internal gates (both labels of an internal
wire are individually reachable), so the output-1 label is not authenticated. Repairing that is
exactly WE (indeed obfuscation) for the residual circuit with cheap `Enc`. **Verdict: dead;
reduces to the original problem with fewer inputs.** Tables of hashes over halves are
evaluation-only and fall under section 1.

**(2) Merkle puzzles / time-lock flavour.** Merkle's quadratic gap needs two parties with
independent secret randomness that meet by collision. WE is non-interactive: only `Enc` is
randomized, and the decryptor's sole advantage is `w`. A puzzle opened by `w` through evaluations
of `φ` is covered by section 1; a time-lock opened by anyone after `T` steps gives the false-
statement adversary the same opening, so `T ≥ 2^128` and then `time(Dec) ≥ T` unless `w`
shortcuts it, which again is WE for the shortcut predicate. **Verdict: dead.**

**(3) SAT algorithms faster than brute force inside `Enc` ("decide, then encrypt").** Then
`N ≈ time(SAT algorithm)` with the scheme statistically secure and assumption-free. For general
circuits of size `32n` (here `2^12 = 32·128`) no algorithm better than `2^n / superpoly(n)` is
known (the savings results for general circuits stop near size `3n`; Williams-type savings
need ACC-like or formula structure). Tseitin plus PPSZ works on `n + s = 4224` variables, about
`2^{1600}`. Gray-code incremental evaluation recomputes the fan-out cone of the flipped input, which
is the whole circuit in the worst case (a balanced tree over all inputs feeding the rest), so it
saves only constants. **Verdict: `N ≈ 2^128 · s / O(1)` is the floor of this route; it is the
baseline, not an improvement in the exponent.**

**(4) Cheap OWF/PRG + exhaustive search over a reduced space.** Any reduction of the searched
space that uses `φ` only by evaluation is section 1 (`q ≥ 2^125`). A reduction that uses the
description of `φ` (partial evaluation, restriction, simplification) still needs a residual WE as
in (1), or a SAT speed-up as in (3). **Verdict: dead.**

**(5) Lower bounds.** Section 1 is a proved lower bound for the relativized (evaluation-only)
class. An unconditional lower bound for *white-box* schemes (say `N ≥ 2^120` for every correct
and secure scheme) is out of reach: it would assert a concrete attack of cost `< 2^128·adv²` on
every cheap candidate (including iO-based WE at concrete parameters), a concrete lower bound of a
kind no current technique proves.

## 3. What the concrete regime does buy

* **The proof side, not the algorithms.** As in note `pq-we-hybrid-count-barrier`, a reduction
  with `2^128` hops costs `2·128` bits of advantage, so premises around `384` bits suffice. The
  counting of statistical versus computational hops is the theorem
  `AdvancedEncryption.WE.Hybrid.stat_hops_carry`.
* **Exponential-time honest algorithms are allowed, but must be non-black-box.** By section 1, a
  scheme with `N < 2^120` must read the *description* of `φ`, as homomorphic-evaluation
  candidates (BGG+/GGH15 walks) do. Exponential time can be spent on `2^{n−a}` residual instances
  only if each residual WE is itself non-black-box and cheap.

## 4. Best lead (open)

A fine-grained non-black-box route with `time(Enc) ≈ 2^{64} · poly(s)`: **arithmetization over
half the inputs** (batch evaluation in the style of Williams' MA protocols for #SAT). With
`x = (y, z)`, `|y| = |z| = 64`, put the `2^64` values of `y` on a low-degree curve `γ` and let
`P(t) = Σ_z C̃(γ(t), z)`; `Enc` can evaluate `P` at a point of its choice in about `2^64 · s`
field operations, which is non-black-box and so not covered by section 1. The concrete SZK form
of the barrier (statistical WE with `Enc` cost `T` yields a Statistical-Difference instance with
samplers of size `T`, hence an AM-type protocol for UNSAT of cost `poly(T)`) does not forbid
`T ≈ 2^64·poly(s)`, because MA protocols for counting satisfying assignments with about `2^{n/2}`
cost exist for wide circuit classes. Two obstacles must be solved before this is a construction:
(a) the degree of a naive arithmetization of a depth-`d` NAND circuit is `2^d` (up to
`2^{4096}` here); the proof-system fix gives the verifier per-gate polynomials from a prover, which
a non-interactive encryptor does not have; (b) turning a proof system for the *complement*
(UNSAT) into an encryption that a single witness opens is the instance-dependent-commitment
problem, open for SAT. Both should be checked against the exact statements in the literature
before formalizing anything.
