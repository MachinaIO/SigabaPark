---
title: "A simultaneous terminal-block bound for Haar lattices"
refs: []
tags: [lattice-attack]
---
*Moved from `docs/research/wall1_sublattice.md` (core v0.1.2).*

# A simultaneous terminal-block bound for Haar lattices

Let $L$ have invariant probability measure on unimodular lattices in $\mathbb R^n$, let $2\le b<n$ be the terminal block dimension, and put $k=n-b$. For a primitive rank-$k$ sublattice $W$ write $s=\det W$ for covolume in its span and $Q_W$ for the orthogonal projection of $L$ onto its orthogonal complement. A basis of $W$ extends to one of $L$, so the block triangular volume formula gives $\det Q_W=1/s$.

For $V_i=\pi^{i/2}/\Gamma(1+i/2)$ put $Z_1=1$ and $Z_i=\zeta(i)$ for $i>1$. Define
$$
 A(m,j)=\frac1m {m\choose j}\prod_{i=1}^j
 \frac{V_{m-i+1}Z_i}{V_i Z_{m-i+1}}.
$$

**Terminal minimum.** For every $X,r>0$ the probability that some such $W$ has $s\le X$ and $\lambda_1(Q_W)\le r$ is at most
$$
 \min\left\{1,\ A(n,k+1)(Xr)^n,\
 \frac{n}{n+1}A(n,k)A(b,1)X^{n+1}r^b\right\}.
$$
In particular either of the two nontrivial terms being at most $\varepsilon$ suffices for a simultaneous lower bound at confidence $1-\varepsilon$. Equivalently, it suffices that
$$
 X\le\max\left\{\frac{(\varepsilon/A(n,k+1))^{1/n}}r,\
 \left(\frac{(n+1)\varepsilon}{nA(n,k)A(b,1)r^b}\right)^{1/(n+1)}\right\}.
$$
This quantifier includes every prefix selected after inspecting the entire basis. On the good event the first Gram–Schmidt length in each qualifying terminal block exceeds $r$, since its projected basis vector is nonzero.

**Proof.** A shortest vector of $Q_W$ generates a primitive line (a rank-one subgroup). Taking the full inverse image of this subgroup in $L$ gives a primitive rank-$(k+1)$ subgroup $U$ containing $W$, since the quotient by the line is torsion free. Conversely every such $U$ projects to a primitive line. A basis of $W$ completed by a lift of a line generator has volume $t=\det U=s$ times the generator length. Hence failure is equivalent to existence of a flag with $s\le X$, $t\le sr$.

The expected number of primitive rank-$j$ sublattices of determinant at most $H$ is $A(n,j)H^n$. Every failing flag supplies a $U$ with $t\le Xr$, so Markov's inequality gives the first counting bound. For the other bound use the two-rank flag formula. Its expected count in $s\le S,t\le T$ is
$$
 \frac{n}{k+1} A(n,k) A(b,1) S^{k+1}T^b.
$$
These are the one- and two-rank specializations of the Haar mean-value theorem, with unoriented primitive sublattices counted once. [Seungki Kim, Theorems 3 and 5 and Section 5](https://arxiv.org/pdf/2005.10874)

By subtraction on rectangles this gives the mean counting measure with density $n b A(n,k)A(b,1)s^k t^{b-1}$ on the positive quadrant (rectangles determine the locally finite measure). Integrating first over $0<t\le sr$ and then $0<s\le X$ gives the displayed third term because $k+b=n$. Another application of Markov proves the claim.

**Comparison with the geometric-series assumption.** For a descending unimodular profile $g_i=\delta^{n+1-2i}$, indexed from 1 with $\delta>1$, the predicted prefix volume is $X_G=\delta^{kb}$ and the predicted first terminal length is $r_G=\delta^{b-k-1}$. Only this profile prediction is heuristic. The two counting bounds at $(X_G,r_G)$ are exactly
$$
 A(n,k+1)\delta^{n(kb+b-k-1)},\qquad
 \frac{n}{n+1}A(n,k)A(b,1)\delta^{nkb+b(b-1)}.
$$
Thus one can check directly whether the bound reaches a proposed profile. For example at $b=2$ and fixed $\delta>1$ both terms eventually exceed one. Indeed $A(n,n-j)=A(n,j)$ by cancellation of the products, and for fixed $j=1,2$ Stirling's formula gives $\log A(n,j)=-\tfrac j2 n\log n+O(n)$. The positive log powers of $\delta$ in the two terms grow quadratically in $n$. At this cutoff the first counting bound still proves the explicit lower scale $(\varepsilon/A(n,1))^{1/n}/X_G$, whose ratio to $r_G$ is $(\varepsilon/A(n,1))^{1/n}\delta^{-(n-1)}$ for $b=2$. For fixed confidence this ratio tends to zero.

A BKZ application must also control the determinant of the prefix it selects. If that determinant exceeds $X$ with probability $p$, the unconditional failure bound for its terminal minimum increases by at most $p$, by splitting on the cutoff event. The GSA comparison supplies no estimate of $p$. Transfer to a polynomial-modulus ensemble would require a counting bound in that ensemble.

## Independent audit (Nov 2026)

Verdict: **correct** (Kim, arXiv 2005.10874v3, Theorems 3, 5, 8 and Section 5 read). `A(m,j)` equals
Kim's `a(n,d)` with unoriented counting (`A(2,1) = 3/π`); the flag constant `(n/(k+1))A(n,k)A(b,1)`
was cross-checked against `(n/b)A(k+1,k)A(n,k+1)` for all `n ≤ 8`; `n/(k+1)` (flag count) and
`n/(n+1)` (after integrating `t ≤ sr`, `s ≤ X`) are consistent. Gaps: the extension of Theorem 5 from
rectangles to the region `t ≤ sr` is only asserted (valid: locally finite mean measure); the guarantee
needs the selected prefix to have `det ≤ X`, whose probability `p` is not estimated; "vacuous at the
GSA terminal length" holds only asymptotically: at `b = 2` the bound is still non-vacuous up to about
`n = 200` for `δ = 1.005`, `n ≈ 50–100` for `δ = 1.01`. Haar model only; the q-ary case is open.
