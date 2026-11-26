---
title: "Moments of random prime-index sublattices"
refs: []
tags: [lattice-attack]
---
*Moved from `docs/research/rerandomization.md` (core v0.1.2).*

# Moments of random prime-index sublattices

## The exact finite average

Let $B=Mℤ^d$ have covolume $D=|\det M|$, with $d≥1$, and fix a prime $p$.
Write $v(x)=M^{-1}x\bmod p$. Draw a uniformly random **nonzero** form $c$ on
$𝔽_p^d$ and take $L_c=\{x∈B:c(v(x))=0\}$. This is uniform over index-$p$
sublattices. Indeed the composite map onto $𝔽_p$ is surjective. Conversely each
index-$p$ quotient is cyclic of order $p$, and its $p-1$ identifications with
$𝔽_p$ give exactly the forms with that kernel.

**Tuple moment theorem.** For an ordered tuple $x∈B^t$ let $r(x)$ be the dimension
of the span of its residues. For every nonnegative weight $F$,
$$
  𝔼\sum_{x∈L_c^t}F(x)=\sum_{x∈B^t}F(x)w_{r(x)},\qquad
  w_r=\frac{p^{d-r}-1}{p^d-1}.
$$
Indeed the common annihilator has dimension $d-r$, and deleting its zero element
leaves $p^{d-r}-1$ forms. Sum the resulting probabilities, using monotone
convergence for infinite support. Restrictions such as nonzero, distinct, or
linearly independent entries can all be imposed in the weight.
For one, two and three entries, group the sum by $r=0,…,\min(t,d)$.
In particular ordinary second and third moments of a set count use its product
indicator including diagonals. The coefficient differs from $p^{-r}$ by exactly
$-(1-p^{-r})/(p^d-1)$.

For one nonzero vector the coefficient is one on $pB$ and $w_1$ elsewhere.
Support at norms strictly below $pλ_1(B)$ removes the former term completely.
Even there the coefficient is $w_1$. Using $1/p$ would count the zero form
among the possible draws.

## A quantitative first-moment comparison

Normalize $L_c$ by dividing lengths by $a=(pD)^{1/d}$. For a bounded measurable
region $A$ in normalized space put $S=aA$. Write $N_H(S)$ for its nonzero
point count in $H$. Then the expectation is
$w_1 N_B(S)+(1-w_1)N_{pB}(S)$. The continuum target is $|A|$, since
$w_1+(1-w_1)p^{-d}=1/p$. Thus its signed error is exactly the same weighted
sum of the two discrepancies $N_H(S)-|S|/\det H$.

For example let $S$ be a shell of inner and outer radii $u,v$, with $0<u<v$.
Let $b$ be the covering radius of $B$, and let
$E(s)=κ_d\sum_{z∈\{u,v\}}((z+s)^d-\max(0,z-s)^d)$, where $κ_d$ is unit ball volume.
The absolute error is at most
$$
 w_1 E(b)/D + (1-w_1) E(pb)/(p^d D).
$$
Indeed tile by Voronoi cells centered at points of $H$. Cells with centers in
the shell have total volume $N_H(S)\det H$, and their union differs from the
shell only within the covering radius of either boundary sphere. The two
annuli have combined volume at most the displayed numerator. When
$v<pλ_1(B)$, the exact zero count for $pB$ gives the sharper option of
replacing $E(pb)$ by $|S|$. A bound smaller than $ε|A|$ suffices for
relative error $ε$ in the expectation.

For higher moments a precise sufficient comparison is as follows. Let $C_r$
sum the desired normalized tuple weights over the modular rank-$r$ stratum
of $B^t$ (evaluate the weight at $x/a$). Given a proposed continuum moment
$I$, decompose it into contributions $I_r$ summing to $I$. Bounds
$|w_r C_r-I_r|≤δ_r$ imply absolute error at most $\sum_rδ_r$ by the theorem.
In particular an ordinary volume approximation on the full-rank stratum alone
leaves every lower-rank contribution to control. Real dependence and modular
dependence can differ. If all coordinate rows have Euclidean length at most
$H≥1$ and $H^t<p$, every nonzero minor remains nonzero modulo $p$ by
Hadamard's inequality. Physical radius $v$ gives only $H=\max(1,\|M^{-1}\|v)$.
Even equality of ranks supplies no discrepancy estimate on those strata.

## A deterministic obstruction and the cost of survival

For every fixed $d≥2,p$, take $B=\operatorname{diag}(η,η^{-1},1,…,1)ℤ^d$
with $0<η<1$. Its covolume is one and its orthogonal basis in increasing order
of length is even HKZ reduced (in each projected suffix the first axis is
shortest). Every normalized draw contains all multiples of
$p^{1-1/d}η e_1$. In any fixed normalized shell with radii $0<R_-<R_+$
the number of these points is at least
$2((R_+-R_-)/(p^{1-1/d}η)-1)$, by counting integers in an interval.
This diverges as $η↓0$ while the shell volume stays fixed. Taking $η$
sufficiently small forces failure of S1 for **every** draw. Even its first
moment has unbounded error at fixed dimension, index, determinant and shell.
The cutoff excluding $pB$ in the one-point corollary need not include the
shell at the normalized sieve radius. This example concerns uniformity over
inputs at finite index. It leaves open limits for a single fixed input as the
index grows.

A physical vector returned in $L_c$ belongs to $B$, with its normalized
length multiplied by $a$. For exact SVP a fixed shortest vector of $B$ is
primitive and survives with probability $w_1$. In $d≥2$, independent trials
with an exact sublattice oracle therefore suffice with failure at most
$(1-w_1)^m$ after $m$ draws by taking the shortest output. For a unique
shortest pair this failure probability is exact. Expected trials to first
survival are $1/w_1=Θ(p)$; in dimension one survival is impossible. An actual
random-input solver would also need a success guarantee on draws containing
the target. A failure probability bound exceeding $w_1$ alone cannot give
that guarantee. If each trial cost $2^{αd+o(d)}$, a prime $p=2^{cd+o(d)}$
would add $c$ to the time exponent for this repetition scheme.

Consequently neither the conditional T1 cost nor the faster search exponent in
the companion sieving note follows for arbitrary projected blocks. The
counterexample already breaks the shell population premise. On a restricted
family where first moments agree, the pointwise simultaneous lens bounds S2
would still require a tail argument. The finite average establishes neither
such bounds nor a shape-independent choice of index and retry budget.

## Lean scope

`SigabaNeo.Rerand.nonzeroKernelCount` counts the admissible nonzero forms.
`SigabaNeo.Rerand.meanValue` gives the normalized weighted sum for a finite
support of any arity over nonnegative real weights. Instantiate its matrix
with the reduced coordinate rows of the tuple. The Euclidean estimates,
infinite-support extension and sublattice interpretation above are paper proofs.
