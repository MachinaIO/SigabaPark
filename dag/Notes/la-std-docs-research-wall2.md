---
title: "A dual obstruction surviving input-dependent index selection"
refs: []
tags: [lattice-attack]
---
*Moved from `docs/research/wall2.md` (core v0.1.2).*

# A dual obstruction surviving input-dependent index selection

Consider a determinant-one parent in dimension d ≥ 2 with a nonzero dual
vector of length 1/T. Let H be *any* index-p sublattice, and normalize H to
determinant one by setting L = p^(-1/d) H. Fix a target width R > 0 (for
example the radius of a volume-one ball). For 0 < ε < 2, a necessary
condition for smoothing at width R is

    p ≥ [T sqrt(log(2/ε)/π) / R]^d.

Indeed, duality reverses inclusion, so the parent witness belongs to the
dual of H. Scaling the primal by p^(-1/d) scales its dual by p^(1/d).
The two opposite witnesses are distinct and contribute exactly
2 exp(−π R² p^(2/d)/T²) to the nonzero dual Gaussian mass. Smoothing
requires that this contribution be at most ε. Taking logarithms,
rearranging positive factors, and raising to the power d gives the claim.
The argument holds for every index, including a composite index selected
after inspecting the entire basis.

The rectangular lattice with diagonal basis lengths T, 1/T, 1, …, 1
has determinant one and dual witness (1/T,0,…,0). For any proposed cap
P ≥ 1, taking T > R P^(1/d) sqrt(π/log(2/ε)) rules out smoothing
for every index at most P and every orientation of the sublattice.
In particular, a determinant-only index budget cannot suffice uniformly.
A profile-dependent choice can exceed this necessary bound. The bound
gives no sufficiency statement for such a choice.

## Formal scope and remaining question

`SigabaNeo.Wall2.dualPair_exceeds` formalizes the scalar Gaussian comparison
at all widths 0 ≤ s ≤ R given an exponent budget at R. Dual containment,
determinant normalization, the rectangular example, and the explicit
index bound above are paper arguments.

The example quantifies over worst-case block shapes. Its probability under
a planted input and a prefix chosen by BKZ is undetermined. A
high-probability smoothing invariant on those selected blocks, the static
sieve hypotheses there, and the requested estimator cost remain open here.
