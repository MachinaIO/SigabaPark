---
title: "Smoothing an exact block trajectory"
refs: []
tags: [lattice-attack]
---
*Moved from `docs/research/wall1_smoothed.md` (core v0.1.2).*

# Smoothing an exact block trajectory

Uniform tie-breaking removes the axis discrepancy in the three-dimensional example of [Part 14](wall1_dynamics.md). It fails one step later in dimension four. A single generic metric also need not restore a covolume-only transition, even when conditioning on the exact perturbed covolume. The two examples below use iid binary checks.

## Fresh uniform choices at each insertion

Take the kernel in integers of a uniform binary row $(a,b,c,d)$. Use consecutive coordinate blocks of size two, starting from a basis adapted to the coordinate flag. Insert a uniformly chosen shortest line at each step, using fresh coins. Complete the insertion within its block. Consider the histories $H_{12},H_{13}$ that first select axis 1 and then select projected axis 2 or 3, respectively. The third block is the projection of the full lattice off the two selected axes. Here and below an axis selection in these histories means selecting its **unit** generator.

In each history both deleted coefficients vanish. Thus the last block is a plane parity kernel. Write $r$ for its remaining coefficient among the first three. Its area is two exactly when $(r,d)\ne(0,0)$, and its squared minimum is two exactly when $(r,d)=(1,1)$. Indeed the latter kernel excludes both unit axes and contains a diagonal. The likelihoods of the histories given the input are

| History | Required zeros | Remaining coefficient | Likelihood at zero | Likelihood at one |
|---|---|---|---:|---:|
| $H_{12}$ | $a=b=0$ | $c$ | $1/4$ | $1/2$ |
| $H_{13}$ | $a=c=0$ | $b$ | $1/4$ | $1$ |

To check the table, when all three coefficients vanish each visited plane has two shortest axes. For $(a,b,c)=(0,0,1)$ only the first decision is tied. For $(0,1,0)$ both decisions are forced. Projection after the first unit selection drops its coordinate, so this calculation is independent of the within-block completion. If the two likelihoods are $s,t$, the desired conditional probability given area two is $t/(s+2t)$ by summing the three nonzero pairs. The answers are **2/5 and 4/9**, a gap of $2/45$. This also covers independent uniform choices among primitive lines of length at most $h\lambda_1$ for every $1\le h<\sqrt2$. On a plane with a unit vector, every longer vector has length at least $\sqrt2$. A unit selection is impossible when its coefficient is nonzero.

## One continuous metric for both queries

Return to the three-dimensional binary row $(a,b,c)$ and the two overlapping blocks of Part 14. Fix $0<e<1/100$. Sample a symmetric matrix $B$ uniformly in the Frobenius ball of radius $e/10$ about $\mathrm{diag}(1,1+e,1)$, independently of the check. Use the squared norm matrix $G=S B$, with $\log S$ independent and uniform on $[0,10e]$. This full-dimensional perturbation tends uniformly to the identity. The anisotropy of its center is intentional.

Write $X,Y$ for first selecting unit axes 1 and 2. The eigenvalues of $B$ lie in $[1-e/10,1+1.1e]$. Thus a Euclidean squared length at least two loses to any available unit, and $B_{11}<B_{22}$ forces axis 1 when both are available. Consequently $X$ means $a=0$, and $Y$ means $a=1,b=0$. When both coefficients are one neither unit is possible. These histories depend only on the row.

For selected unit $i$, let $k$ be the index of the residual binary plane kernel (one or two). In coordinates modulo that unit the quotient metric is the Schur complement of $G_{ii}$. Its covolume is
$$
 D=k S C_i,\qquad C_i=\sqrt{\det B/B_{ii}}.
$$
Indeed the residual integer coordinates range over precisely that plane kernel. The quotient quadratic form for $B$ is the minimum over real lifts of the squared norm, so it obeys the same two spectral bounds as $B$. Hence $1-e/10\le C_i\le1+1.1e$ by taking the square root of its two-dimensional determinant.

Consider the interval $J=2[\exp(2e),\exp(8e)]$. Index one cannot reach it since $\exp(10e)(1+1.1e)<2$. For index two, every possible $C_i$ gives the same density $1/(10eD)$ throughout $J$, by the log-uniform scale and $-2e<\log C_i<2e$. Thus conditioning on the *measured* area at almost every $D\in J$ leaves the relative weights of all index-two rows within either history unchanged. This interval has positive probability. The event that the perturbed terminal squared minimum exceeds $3/2$ distinguishes residual row $(1,1)$ exactly. Its minimum is at least $2(1-e/10)$ there, and an available unit elsewhere has squared norm at most $\exp(10e)(1+1.1e)<3/2$.

Given $X$, the possible index-two residual rows are $(0,1),(1,0),(1,1)$ with equal weights. Given $Y$ they are $(1,0),(1,1)$ with equal weights. The conditional tail probabilities are therefore **1/3 and 1/2** on the same interval of perturbed areas. Any common area-dependent prediction incurs absolute error at least $1/12$ on one history at almost every such area. This disproves sufficiency under generic smoothing in general. It leaves open more restrictive perturbation laws, including orthogonally invariant noise centered at the identity.

## What genericity gives for an adaptive prefix

Fix a full-rank lattice and draw a metric with a density on positive definite forms. Almost surely every projected lattice block with lattice-generated prefix has a unique shortest unoriented line simultaneously. For a fixed prefix choose real coordinates adapted to its span. Squared lengths of quotient classes are rational functions of the metric entries by the Schur complement formula, with positive denominator. Equality for two classes distinct up to sign gives a nonzero polynomial after clearing denominators. Indeed one may choose a block diagonal metric with arbitrary positive quotient form, and the two rank-one outer products differ. The polynomial zero set is null (induct on the number of variables using the univariate root bound and Fubini). There are only countably many lattice-generated prefixes and pairs of classes. This argument applies conditional on each discrete lattice input when the noise has a conditional density.

For a fixed finite schedule of exact shortest-line queries and a metric-independent completion rule given the selected coefficients, the discrete transcript is locally constant at each such tie-free metric. For one fixed block the quotient lattice is discrete, since the prefix is spanned by part of a lattice basis. On a sufficiently small metric neighborhood, all quotient squared norms stay between one half and twice their center values by minimization over lifts. Only the finitely many classes within four times the center squared minimum can then compete. Strict comparisons against the other lines persist locally, and induction applies to the finite schedule. Averaging hence weights transcripts by the noise mass of their decision regions. For atomic rational perturbations the null-set argument alone supplies no probability estimate.

Neither uniqueness nor local stability identifies the minimizing line with a marked plant. A fixed prefix also preserves the divisibility of the plant class under a change of quotient metric. The missing random-input estimate concerns the joint probability that the selected quotient contains a nonzero primitive plant class and every competing line has larger minimum. These examples give no block-size or running-time bound for the planted ensemble.


## Independent audit (Nov 2026)

Verdict: **correct**. (1) re-enumerated (2/5 vs 4/9); (2) generic uniqueness (nonzero tie polynomial, countable union of null
sets) and local stability (quotient forms within factor 2, finitely many competitors) are valid for metric-independent
completions; (3) checked by hand and by Monte Carlo (e = 0.009, 200k samples: ≈ 0.331 vs 0.501). Nit: lattice-generated
prefixes suffice for discreteness (primitivity not needed). Cross-reference: the audit of wall1_coupling.md found that in the
4-dimensional example conditioning on the full in-block profile removes the discrepancy; whether the same holds for the
anisotropic example of (3) is being examined in docs/research/wall1_profile.md.
