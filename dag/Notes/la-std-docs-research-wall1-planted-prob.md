---
title: "A deterministic obstruction to the all-prefix probability bound"
refs: []
tags: [lattice-attack]
---
*Moved from `docs/research/wall1_planted_prob.md` (core v0.1.2).*

# A deterministic obstruction to the all-prefix probability bound

At block size 406, the probability that **some** primitive prefix below the Part 6 determinant cutoff has a nonprimitive, nonzero planted projection is exactly one at each plain-LWE shape in the table below. This holds for every matrix and every planting with coordinate bound 3. The quantifier over all primitive prefixes is essential. The construction gives a prefix of a basis of the planted lattice, with no reducedness claim for that basis.

## A witness outside the last-coordinate hyperplane

Write the embedding as $L=L_0\oplus\mathbb Zu$ as abelian groups, where $u=(e,s,1)$ and $L_0$ is the last-coordinate-zero lattice. Its rank is $N=m+n=d-1$ and its determinant is $D=q^m$, since the error-coordinate identity block makes the syndrome map surjective. The same determinant holds for $L$ by base times height.

Choose a fully HKZ-reduced basis $b_1,\ldots,b_N$ of $L_0$ and write $V_j$ for its first $j$ vectors' integer span, $H_j=\det V_j$, with $H_0=1$. For $1\le k\le N$ take
$$
 W=V_{k-1}+\mathbb Z(2b_k+u).
$$
Replacing $u$ with $2b_k+u$ in the extended basis is unimodular. Reordering that basis exhibits $W$ as primitive, with $W\cap L_0=V_{k-1}$. The quotient has the class of $b_k$ as a basis element and $[u]=-2[b_k]$. Its orthogonal realization therefore has planted multiplicity exactly two. Projecting the last generator off $V_{k-1}$ and applying the triangle inequality gives
$$
 \det W\le 2H_k+\|u\|H_{k-1}.
$$
For a small illustration take $L_0=\mathbb Z(1,0)$ and $u=(0,1)$. Modulo $(2,1)$ the planted class is twice the negative horizontal generator. The construction above controls the analogous witness volume in large dimension.

## Exact cutoff comparison

Use base-two logarithms throughout. Put $c_h=\frac12\log_2\bar\gamma_h$ for the Hermite bounds in Part 6. At step $j$, $h=N-j+1$, the remaining projected lattice has determinant $D/H_{j-1}$. HKZ chooses a shortest vector there, so
$$
 \log_2 H_j\le (1-1/h)\log_2 H_{j-1}+\log_2(D)/h+c_h.
$$
For the *lower* bound on the Part 6 cutoff $X$, take the feasible normalized log-prefix sequence $S_i=i(d-i)/160$. Indeed its successive slopes decrease by $1/80$, so the first slope of an $h$-block exceeds its average by $(h-1)/160$. The script checks $c_h\ge(h-1)/160$ for every $2\le h\le406$. Both endpoints vanish, hence the common upper envelope dominates $S_k$. Consequently $\log_2 X\ge(k/d)\log_2 D+k(d-k)/160$. Feasibility in the linear inequalities suffices for this comparison. [Part 6 envelope](wall1_prefix.md)

| $n$ | $m$ | $d$ | $k=d-406$ | upper bound on $\log_2\det W$ | lower bound on $\log_2 X$ |
|---:|---:|---:|---:|---:|---:|
| 512 | 188 | 701 | 295 | 1614 | 1666 |
| 512 | 511 | 1024 | 618 | 4838 | 5145 |
| 512 | 512 | 1025 | 619 | 4848 | 5157 |

Here $q=3329$ and $\|u\|\le\sqrt{9N+1}<128$. The script bounds $\log_2 q$ between 11.6 and 11.8 by integer powers. It encloses $\bar\gamma_h^h$ using the exact Part 6 constants through dimension eight and $(2/\pi)^h\Gamma(2+h/2)^2$ thereafter, substituting $3<\pi<22/7$ after simplifying half-factorials. For a positive rational $a/b$, the difference of numerator and denominator bit lengths plus one bounds $\log_2(a/b)$ above. Iterating the increasing recurrence and using $x+y\le2\max(x,y)$ gives the displayed outward-rounded integers. Run [the exact arithmetic calculation](../../python/wall1_planted_prob.py) with Python 3.

## What conditioning on a horizontal prefix gives

If $W\subset L_0$ is chosen using $A$ alone, last coordinate descends to an integer functional taking value one on $[u]$, so multiplicity is one. Let $P$ be the horizontal orthogonal projector off $W$, of rank $r=\beta-1$, and $x=(e,s)$. The projected plant is $(Px,1)$. For centered iid bounded coordinates of variance $v$ and fourth moment $M$, its squared length has mean $1+vr$. For $t>0$ the probability of deviation at least $t$ from this mean is at most
$$
 \min(1,\max(M-v^2,2v^2)r/t^2).
$$
Indeed the centered diagonal terms of $x^TPx$ and its off-diagonal monomials are pairwise uncorrelated by independence and centering. Their variances sum to $(M-v^2)\sum P_{ii}^2+4v^2\sum_{i<j}P_{ij}^2$, and $\operatorname{tr}(P^2)=r$. Apply Chebyshev. This is concentration about a deterministic mean conditional on the prefix.

More explicitly, set $Y=P L_0$ and let $p(x)$ be the planting mass. The conditional expected count of all off-line vectors at most as long as the projection is
$$
 \sum_x p(x)\sum_{|t|\le\sqrt{1+\|Px\|^2}}\ 
 \sum_{y\in Y\setminus\{0\}}\mathbf1\{\|y+tPx\|^2+t^2\le1+\|Px\|^2\},
$$
where $t$ is integral. Each vector has the unique form $(y+tPx,t)$, with $y=0$ exactly on the planted line. The sums are finite because $W$ is primitive and $Y$ is a lattice. Even exact averaging of this count over horizontal prefixes using modular membership probabilities would leave the deterministic nonhorizontal witness above.

The 2016 estimate of 406 uses a modeled projected length. At the three tested shapes the proposed simultaneous event of success has probability zero at 406. The existing plain-model certificate at $m=188$ gives $\beta=d=701$ with success probability at least $1-2^{-63}$, a difference of 295 in block size. This calculation establishes neither a minimum over intermediate block sizes nor a failure probability for the prefix selected by BKZ. A tighter determinant cutoff would need a fresh comparison with the witness bound. [Existing certificate and estimator conventions](ratio_unique.md)


## Independent audit (Nov 2026)

Verdict: **correct**, no gaps. The witness `b_1..b_{k−1}, 2b_k+u` is an initial segment of a basis of `L` (so `W` is primitive
in `L`, rank `k = d−β`), `[u] = −2[b_k]` gives `a = 2`; the determinant certificate (HKZ recurrence with exact/Blichfeldt
Hermite bounds, bit-length bounds) holds for every `A`; the Part 6 cutoff bound is valid; the script reproduces
1614/1666, 4838/5145, 4848/5157. The fixed-subspace section assumes i.i.d. coordinates for `e` and `s` together (take
the maximum of moments otherwise). Scope: only the all-prefix event; nothing about the prefix BKZ selects.
