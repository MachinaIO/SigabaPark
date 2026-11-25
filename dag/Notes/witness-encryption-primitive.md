---
title: Witness encryption as a Sigaba Neo primitive (modelling choices)
refs: [definition:WE]
tags: [primitive, witness-encryption]
---
`Definitions/Def_WE.lean` defines witness encryption `AdvancedEncryption.WE R p` as a Sigaba Neo
primitive, following Definition 2.1 of Hair and Sahai, *Witness Encryption via Prime-Order Generic
Groups* (arXiv 2609.18275v3), itself after Garg, Gentry, Sahai and Waters (STOC 2013). The same
file is `AdvancedEncryption/WE.lean` in the core repository.

## What is defined

* `WE.Relation`: the NP relation, as statements and witnesses with their bit-string encodings,
  the relation `rel`, and a description word given to the algorithms. `L = {φ : ∃ w, rel φ w}`.
* Algorithms: `Enc(φ, β)` (randomized, outputs `ct`) and `Dec(φ, w, ct)` (deterministic, outputs
  `β`; any output variable other than `[false]`/`[true]` is `⊥`). One-bit messages, no setup.
* `Correct`: for every `(φ, w)` with `rel φ w` and every `β`,
  `Pr[Dec(φ, w, Enc(φ, β)) = β] ≥ 1 − 2^{-κ}`.
* `FalseStatementSecure`: for every `φ ∉ L` and every explicit adversary `A` (a machine without
  oracles, given `(1^λ, 1^κ, desc)`, `φ`, `ct`),
  `2^λ · (Pr[A(Enc(φ,0)) = 1] − Pr[A(Enc(φ,1)) = 1])² ≤ cost A`. Nothing is required for `φ ∈ L`.
* Cost: `time(Enc) + time(Dec) + descLen(Enc) + descLen(Dec)` (one run each: the two algorithms run
  equally often, so no run count is a parameter).

## Modelling choices

1. Negligible functions become concrete bounds: `1 − 2^{-κ}` for correctness and
   `cost / advantage² ≥ 2^λ` for security, as in the other Sigaba Neo primitives.
2. The adversary is quantified after `φ`, which models the paper's nonuniform adversary; its
   description length counts in its cost.
3. Standard model. The generic-group model in which the paper proves its construction is a
   property of that construction, not of Definition 2.1.
4. Polynomial-time decidability and polynomial balance of `R` are asymptotic and are not part of
   the propositions; they are properties of the concrete relation chosen for an instance.
5. Implementations may specialize to the fixed parameters; the description lengths in the cost
   penalize hard-wired tables (for example a table of `L`).

## Notes for instances and designers

* The statements and witnesses of an instance should have bounded length. A clocked `Enc` reads
  only a prefix of `φ`; with unbounded statements, two statements sharing a long prefix, one in `L`
  and one not, make false-statement security unattainable (and likewise `Dec` with long witnesses
  for correctness).
* At fixed parameters `Enc` can decide `L` by brute force (or by a hard-wired table), which
  satisfies both propositions trivially. Such implementations are valid but costly; an instance
  should choose a statement space for which deciding `L` is far more expensive than the intended
  constructions.
* `κ = 0` or `λ = 0` make the respective proposition trivial; instances should fix positive values.
* This node is a family over `R` and `p`. A concrete instance (for example bounded-size circuit
  satisfiability with `λ = κ = 128`) will be a separate definition node declaring `P`, the
  registry `R` and `SubmissionProp`.
