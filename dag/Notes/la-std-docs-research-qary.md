---
title: "Mean values and lens fibres for random q-ary lattices"
refs: []
tags: [lattice-attack]
---
*Moved from `docs/research/qary.md` (core v0.1.2).*

# Mean values and lens fibres for random q-ary lattices

The companion Lean module proves Q1 for finite support, Q2 for Euclidean row norms,
and exact first and second moments and variance for finite shells. The lens estimates
and modular-deficit calculations below are paper arguments.

## Q1, Q2 and shell counts

Sample all entries of an n by m matrix independently and uniformly modulo the prime q.
Conditioning on full row rank would change the distribution. For an integer tuple X with
k rows, let r be its rank after reduction. Each row of A belongs to the kernel of X with
probability q to the power −r by rank-nullity. Thus the mean weight contributed by X is
F(X) times q to the power −nr. In Lean, `meanValue` accepts any finite index set. Index
by the support of F and use the entrywise reduction map to recover Q1.

For Q2, select independent spanning columns, then independent spanning rows of the
restricted matrix. This gives a nonzero square minor of order equal to the rank.
Over either field, a nonzero minor gives a lower bound on the rank. If all row norms
are at most R and R ≥ 1, Hadamard bounds the absolute value of every order-d minor by
Rᵈ ≤ Rᵏ. Under Rᵏ < q every minor has the same vanishing status over both fields.
The Lean proof uses the absolute volume-form bound in the standard Euclidean basis.

Let S be a finite shell excluding zero, contained in the closed ball of radius R.
Use the outer radius for R when applying the result to a two-sided shell.
Write N = |S|, p = q⁻ⁿ and C = |S ∩ ker A|, with the kernel taken modulo q.
Then E[C] = Np if R < q. For R² < q, let D count the **ordered** rationally
proportional pairs in S², including equal and opposite vectors. Q2 gives rank one
on these D pairs and rank two on the others. Consequently

    E[C²] = Dp + (N² − D)p²
    Var(C) = Dp(1 − p).

Equivalently D is the sum of squared shell occupancies of rational lines through zero.
Lean expresses the second moment and variance as exact rational-rank sums.
Its shell theorems assume R ≥ 1. For 0 ≤ R < 1 the nonzero integer shell is empty.

## Q3 in a sufficiently large radius regime

There is a deterministic sufficient condition that avoids a local limit theorem.
Write S for the shell of radii R ± t, t = wR. Set D = ‖d‖, δ = √m/2, and V(t)
equal to the volume of the intersection of two such shells at distance D.
If δ < t, unit cubes centered at the counted integer points give

    V(t − δ) ≤ count ≤ V(t + δ).

Indeed rounding changes each distance by at most δ. This applies even to sparse
centres. The following bounds quantify the price of this argument. Assume m ≥ 3,
R/2 ≤ D ≤ 3R/2 and t + δ ≤ R/32. In the two distance variables a and b the volume
element is a constant times

    J(a,b) da db = (ab/D) h^(m−3) da db,
    h = sqrt(((a+b)²−D²)(D²−(a−b)²))/(2D).

To see this, use the axial coordinate z and transverse radius h about the line of
centres. The absolute Jacobian of (z,h) ↦ (a,b) is Dh/(ab), and transverse polar
coordinates contribute h^(m−2). The entire square [R−t−δ,R+t+δ]² satisfies the
strict triangle inequalities. Both partial derivatives of log J have magnitude
at most 10m/R there. Indeed the derivative of log h in a is the difference of
(a+b)/((a+b)²−D²) and (a−b)/(D²−(a−b)²). Their absolute values are bounded by
2/R and 1/R respectively using the stated endpoints. The b derivative obeys the
same bound, and 1/a, 1/b ≤ 2/R.

Rescale the distance square about (R,R) by 1 ± δ/t. Each coordinate moves by
at most δ. Integrating the resulting pointwise bounds gives

    (1−δ/t)² exp(−20mδ/R) ≤ count/V(t) ≤ (1+δ/t)² exp(20mδ/R).

In particular δ/t ≤ 0.01 and 20mδ/R ≤ 0.06 imply the requested ten percent
accuracy. For w comparable to 1/n and m ≥ n this holds eventually if R/m^(3/2)
tends to infinity. At the Gaussian-heuristic radius this requires q^(n/m)/m
to tend to infinity, a sufficient parameter choice. The analogous higher moment
integrands still require their own boundary estimates, including configurations
where constraints are nearly dependent.

Support size alone does not control arithmetic spacing. For d = g(1,…,1),
the difference of the two squared distances lies in mg² + 2gℤ. If m and g are
odd its absolute value is at least g. Thus 4Rt < g precludes every integer
point even when 0 < D < 2R gives positive lens volume. For instance take odd
m ≥ 3, g = 1, R = √m and w = 1/(8m). This example tests a width and support
condition alone. It does not settle the smaller-radius Gaussian-heuristic regime
with the additional q and dimension restrictions in §4. Outside the sufficient
condition above, a local limit proof would need relative error for the tilted
joint law of squared norm and inner product, summed over the actual attainable
lattice in the shell windows, uniformly in d. A central limit theorem with
absolute error gives insufficient control of these small probabilities.

## Modular coincidences near m = 2n

For rational rank k and modular rank k−r the excess weight per tuple in Q1 is
exactly q^(−nk)(q^(nr)−1). More generally replace k in the leading factor by
the rational rank. Summing this excess over the actual integer tuples is an
exact correction. A deficit occurs precisely when q divides one or more
nonzero Smith invariant factors, with multiplicity counted by the number of
such factors divisible by q.

For comparison take a uniform residue k by m matrix with k ≤ m. Its probability
of rank j is exactly

    q^(−km) ∏_{i=0}^{j−1} (q^k−q^i)(q^m−q^i)/(q^j−q^i).

Factor the matrix into a full-column-rank k by j matrix and a full-row-rank
j by m matrix, dividing by the number of ordered bases of the intermediate
space. With j = k−r this probability is at most
q^(−r(m−k+r)) / ∏_{h≥1}(1−q^(−h)). Relative to the full-rank per-tuple weight,
its contribution is therefore at most a constant times q^(−r(m−n−k+r)).
At m = 2n the first deficit costs O(q^(−(n−k+1))) on this model.
The infinite product is bounded away from zero uniformly for q ≥ 2.

Integer shell tuples sample residues nonuniformly. A rigorous check for actual
shell data at order two is to group nonzero residues by projective line over
the finite field. When R < q no nonzero shell vector reduces to zero. If the
group sizes are b_L, the exact number of extra rank-one pairs is Σ b_L² − D.
Their excess second moment is (Σ b_L² − D)p(1−p). This formula applies even
when q ≤ R². A uniform asymptotic bound on these occupancies, or on higher
dimensional residue spans at larger k, remains open here.
