---
title: "Macaulay rank for bounded-error Arora–Ge equations"
refs: []
tags: [lattice-attack]
---
*Moved from `docs/research/arora_gb.md` (core v0.1.2).*

# Macaulay rank for bounded-error Arora–Ge equations

Let q be prime, n ≥ 1, and E a known set of d distinct field elements, 1 ≤ d < q.
With m independent uniform sample directions in F_q^n, take the public equations
f_j(X) = ∏_{e∈E}(b_j − a_j·X − e). Assume the planted errors belong to E.
The top-degree blocks depend only on A. A zero direction contributes a zero
degree-d block. We omit secret equations and finite-field equations throughout.
Write ρ for the first degree at which the homogeneous ideal of the degree-d
blocks fills the whole homogeneous component, with value ∞ if none exists.

## Two bounds for random directions

For m ≥ n, put P = ∏_{i=0}^{n−1}(1−q^{i−m}). This is the exact probability
that A has column rank n, by exposing its independent uniform columns in order.
On this event, select n independent rows and change variables to their linear
forms Y_i. The selected top forms are scalar multiples of Y_i^d. At degree
t > S = n(d−1), every monomial has an exponent at least d. Subtract d from
that exponent to get a Macaulay row whose only nonzero entry is the chosen
column (up to scaling). Thus ρ ≤ S+1. With just the n pivots, equality holds:
the monomial with every exponent d−1 is missing in degree S. Adding rows can
only lower ρ. On rank failure all forms vanish along a common line over the
algebraic closure, so ρ = ∞. In particular an unconditional mean of ρ at
fixed finite m is infinite, even for very large m. This concerns homogeneous
saturation in degree, not the runtime of a solver on underdetermined inputs.

There is also a many-sample estimate. Write H = binom(n+d−1,d) and
B = ((q^H−1)/(q−1))(d/q)^m. Then Pr(ρ > d) ≤ min(1,B).
Indeed, pair a nonzero column covector v with the coefficients of (a·X)^d.
The resulting polynomial in a has distinct monomials a^α with coefficients
v_α times their multinomial coefficients. Every multinomial coefficient is
nonzero since q is prime and d < q. The polynomial is nonzero of total
degree d, so Schwartz–Zippel bounds its zero fraction by d/q. Independence
gives the m-th power. Union-bound over the projective covectors. Full span in
degree d implies ρ = d. This extends the kernel-witness counting idea in
CenteredRank to the homogeneous block in arbitrary dimension without assuming
uniform errors. It does not count independent rows among shifts of one sample.

Consequently E[ρ | rank A=n] ≤ d + (S+1−d) min(1,B/P).
For instance, when B is small, the conditional degree is close to its minimum.
For m < H the degree-d block cannot have full column rank and the probability
bound is vacuous. Sharper intermediate-degree estimates require controlling
dependencies among Macaulay shifts.

## Affine XL and a field-operation bound

On full column rank, a single affine XL matrix through degree T = S+d
suffices to compute a graded-order Gröbner basis in pivot coordinates. Here
are the degree certificates. Normalize each pivot equation to a monic
univariate g_i(Y_i) of degree d. Its roots are d distinct field elements.
Reduction by the g_i never increases degree, and records multiples of the
g_i of degree at most the input degree. The pivot quotient is the ring of
all functions on the Cartesian product of the root sets, by interpolation.
Its reduced representatives have degree at most S.

For each grid point z rejected by an additional equation f_j, take its
Lagrange indicator L_z, a product of univariate indicators of degree d−1.
Reduction of L_z f_j gives f_j(z)L_z. Since f_j(z) is invertible, L_z is in
the span of truncated Macaulay rows through S+d. These indicators span every
reduced polynomial vanishing on the surviving points. Thus *every* ideal
element of degree ≤ T is in the truncated row span: first reduce by the
pivots, then expand the remainder in indicators.

For a graded order the initial ideal contains all Y_i^d. Its minimal
generators are either pivot powers or monomials with all exponents < d,
so their degrees are at most max(d,S) ≤ T. Each reduced basis polynomial
has that same degree as its leading monomial. Row elimination in descending
monomial order therefore exposes all minimal initial generators and their
reduced tails. This argument covers multiple surviving points. In the unique
solution case the linear relations directly give its coordinates. For fixed
errors independent of A, each wrong secret passes a row with probability
d/q, so the probability of either rank failure or nonunique recovery is at
most (1−P)+(q^n−1)(d/q)^m, capped at one.

With N = binom(n+T,T) columns and R = m binom(n+T−d,T−d) rows, dense
elimination costs O(R N min(R,N)) field operations and O(RN) field elements.
One may expand the m products of linear factors naively in
O(m d (n+1) N) field operations and fill shifted rows by coefficient copies.
Pivot selection and changing coordinates cost O(m n²) field operations.
These are upper bounds for the specified single-matrix procedure. For fresh
independent batches rejected on rank failure, the expected number of batches
to reach this bound is 1/P. Gaussian truncation requires a separate probability
for all errors to lie in E.

## Comparison with the estimator and literature

The repository's gb loop uses coefficients of
(1−z^d)^m (1−z^s)^n / (1−z)^n, omitting the secret factor when s=0.
It scans 1 ≤ k < 2n for a strictly negative coefficient and returns
2 log₂ binom(n+k,k) in the estimator's fixed-point arithmetic. A zero
coefficient does not stop the scan. For m=n and s=0 the series is the
polynomial (1+⋯+z^{d−1})^n. On full rank its first zero is S+1, yet
the loop never finds a negative coefficient. Conversely, for m>H the
coefficient at d is H−m<0, hence the loop selects d if d<2n. The bound B
quantifies when that homogeneous prediction holds. It gives no equality
between d and the affine solving degree or between either operation count
and the estimator's cost. Neither result validates guessing, Gaussian sample
selection, or the entire cost wrapper.

Fröberg's series concerns generic forms. Pardue relates it to semi-regular
sequences over an infinite field. Bardet, Faugère and Salvy analyze
semi-regular systems, and Albrecht, Cid, Faugère and Perret use a regularity
assumption for their LWE complexity estimate. Powers of random linear forms
occupy a structured family. Hodges, Molina and Schlather study the distinct
square-zero algebra in characteristic two. Their obstruction cannot be
transferred directly to these prime-field equations.
[Fröberg](https://doi.org/10.7146/math.scand.a-12092),
[Pardue](https://staff.math.su.se/shapiro/ProblemSolving/Pardue.pdf),
[Bardet et al.](https://homepage.iis.sinica.edu.tw/papers/byyang/2396-F.pdf),
[Albrecht et al.](https://eprint.iacr.org/2014/1018),
[Hodges et al.](https://arxiv.org/abs/1412.7865).

Steiner already uses independent LWE directions, a coordinate transformation
and Macaulay bounds. His Theorem 5.1 analyzes the regime ρ=d under that
hypothesis. The estimate B above provides a sufficient sample condition
for that hypothesis. The grid argument supplies an elementary certificate
for a specified XL matrix. [Steiner](https://arxiv.org/html/2402.07852v1).

## Formal verification boundary

XL.lean proves the unit-row witness and the preceding zero column directly
from the exponent-level coefficient formula for pivot monomials. The coordinate
change, probabilities, interpolation argument, Gröbner extraction and costs
above are mathematical proofs in prose. A sharp intermediate-sample
prediction and a verification of the estimator's numerical exponent remain open.
