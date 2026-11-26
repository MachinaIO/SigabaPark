---
title: "Simultaneous shell statistics for projected blocks"
refs: []
tags: [lattice-attack]
---
*Moved from `docs/research/wall2_simultaneous.md` (core v0.1.2).*

# Simultaneous shell statistics for projected blocks

At the GSA prefix determinant in dimension 700 the expected number of terminal prefixes violating S1 alone exceeds one, by over 140,000 bits in each example below. Thus even an **exact** computation of the bad-prefix mean followed by Markov cannot certify the proposed simultaneous conclusion there. This is an obstruction to the proof method. Large means can arise from rare lattices with many bad prefixes.

## The exact price of counting all prefixes

Write $v_j=\pi^{j/2}/\Gamma(1+j/2)$, $z_1=1$, $z_j=\zeta(j)$ otherwise, and
$$
 A(n,k)=n^{-1}{n\choose k}\prod_{i=1}^k
 \frac{v_{n-i+1}z_i}{v_i z_{n-i+1}}.
$$
Let $1\le k=n-b<n$, let $s=\det W$, and test the terminal quotient after scaling by $s^{1/b}$ to determinant one. Let $p_b$ be the Haar probability in dimension $b$ of a measurable rotation-invariant bad-shape event. This can include all prescribed levels and all marks in S2 and S3′. For Haar input in dimension $n$, the exact expected number of primitive unoriented prefixes with $s\le X$ and bad shape is
$$
 M=A(n,k)X^n p_b.
$$
Consequently the failure probability for *any* qualifying prefix is at most $\min(1,M)$. For $p_b>0$ this method certifies failure at most $\epsilon$ precisely up to $X=(\epsilon/(A(n,k)p_b))^{1/n}$ when using the exact marginal.

**Proof.** Unfold the sum over primitive subgroups to the quotient by the integer stabilizer of the standard rank-$k$ summand (one orbit by basis extension). In block triangular coordinates the diagonal blocks have determinants $s$ and $1/s$ in absolute value. Removing these scales leaves the two special-linear shape factors. At fixed orientation and scale, the block unipotent coordinate ranges over a torus of normalized volume one in integral shear coordinates. The invariant measure on the two diagonal shape factors is product Haar: the parabolic modular character depends only on their determinants, and the block diagonal special-linear actions preserve Lebesgue measure on the shear space. The lower-dimensional lattice quotients have finite invariant volume. Orthogonal factors and the finite orientation identifications disappear in a rotation- and reflection-invariant test (as all tests here are). Thus inserting the quotient-shape indicator multiplies the unmarked integral by $p_b$. The unmarked integral up to $X$ is Kim's $A(n,k)X^n$. The same decomposition gives Haar **prefix** shape when testing that factor instead. This is an identity for a sum over marks. It assigns no Haar law to a prefix chosen by a reduction algorithm. [Kim, Theorem 3 and parabolic integration in §3](https://arxiv.org/pdf/2005.10874)

## An explicit lower bound on the bad marginal

Use the terminal shell of the prescribed sieve, with $w=b^{-2}$,
$R=\sqrt{4/3}\exp(1/\lceil\log b\rceil)v_b^{-1/b}$ and
$H_j=v_jR^j((1+w)^j-(1-w)^j)$. Here the section in dimension $b-1$ uses the **same** width and radius. Set $h=1/10$ and $m=v_b h^b/(2\zeta(b))$. For the three dimensions below,
$$
 p_b(\text{S1 fails})\ \ge\ \frac{m}{4(1+m)}.
$$

**Proof.** Count primitive unoriented dual lines whose generator has length $t\le h$. Their number $D$ has mean $m$ by primitive Siegel integration. Each such line determines a primitive hyperplane lattice in the primal lattice of determinant $t$: the consecutive parallel layers have spacing $1/t$ and the ambient determinant is one. Conversely each primitive hyperplane determines one such dual line. In the mean over these marks its normalized shape is Haar by the preceding prefix-factor calculation, also when restricting $t$ to any interval.

Write $C$ for the number of shell points in the marked hyperplane. At scale $t$, its mean is $u=H_{b-1}/t$. For dimension $d=b-1$, Rogers' pair formula gives variance at most $4\zeta(d-1)u$ for any centered spherical shell of volume $u$ on the normalized lattice. Indeed the dependent-vector integrals, indexed by coprime $q\ge1$, $p\ne0$, are bounded by $u/\max(q,|p|)^d$ by either of the two volume bounds. At most $4j$ pairs have maximum $j$. The independent term is the square of the mean. This also proves the variance estimate for a ball with its origin excluded. [Rogers formula in Han, Theorem 2.1](https://arxiv.org/html/2407.00986v1#S2)

In the table's dimensions $H_b>2^{43}$ and $H_{b-1}/h>10 H_b$ by the displayed volume formulas. Chebyshev gives
$\Pr(C\le1.01H_b)\le4\zeta(b-2)u/(u-1.01H_b)^2<1/2$.
Let $G$ count lines with $C>1.01H_b$. Then $E G\ge m/2$ and every such line forces S1 failure in the full shell. Moreover $E D^2=m+m^2$. For the factorial moment, distinct primitive lines are independent in the linear-algebra sense. Rogers' independent ordered-vector term has product Lebesgue intensity. Restricting both vectors to primitive ones by Möbius inversion scales this by $1/\zeta(b)^2$ (the absolute divisor sums converge for $b>2$), and dividing by four forgets both signs. This gives $E[D(D-1)]=m^2$ on the dual lattice, which is Haar by inverse transpose invariance. Cauchy–Schwarz now gives $\Pr(G>0)\ge(EG)^2/E D^2$, as claimed.

## Numerical comparison

All logarithms in the table are base two. Use $n=700$, $k=n-b$, and the heuristic GSA cutoff $X_G=\delta^{kb}$ with $\delta=((\pi b)^{1/b}b/(2\pi e))^{1/(2(b-1))}$. Only the interpretation of this cutoff as a reduced profile uses GSA. Values are rounded to the nearest 0.1 bit. The last column is the logarithm of the **lower bound** on the expected number violating S1.

| $b$ | $\log X_G$ | $-(\log A)/700$ | $\log(AX_G^{700})$ | $\log m$ | $\log(AX_G^{700}m/[4(1+m)])$ |
|---:|---:|---:|---:|---:|---:|
|100|797.8|237.2|392425.0|−464.8|391958.2|
|200|903.6|400.1|352433.0|−1025.0|351406.0|
|400|688.0|482.5|143846.5|−2244.9|141599.7|

For example, at confidence 99%, even without knowing any shape statistics one can take $\log_2 X\le-(\log_2 A)/700+\log_2(.01)/700$. This works because with probability at least .99 there is no qualifying prefix. At the other end, the exact first moment cannot certify 99% once $\log_2 X> [\log_2(.01/A)+\log_2(4(1+m)/m)]/700$. This necessary ceiling is about 237.8, 401.5 and 485.7 bits respectively. The intermediate cutoffs depend on the actual joint bad marginal. No independence between prefixes was used.

## Interior blocks and the modular ensemble

When $n-k>b\ge2$, a prefix alone does not specify a block. If the quantifier includes *all* primitive rank-$b$ continuations in the quotient with no bound on their determinant, it fails for every qualifying prefix, for every ambient lattice. To see this, choose a quotient basis $e_i$ and take the block generated by $e_1,\ldots,e_{b-1}, e_b+T e_{b+1}$ for integral $T$. This extends to a basis by an integral shear. Its determinant grows linearly in $|T|$ asymptotically, since the wedge with $e_{b+1}$ is nonzero. After normalizing the block determinant, the spacing $a$ along $e_1$ tends to zero. The two rays of this line alone contribute at least $2(2wR/a-1)$ shell points, eventually exceeding $1.01H_b$. A reachable-continuation or second determinant restriction would change this quantifier.

This interior obstruction also holds on every full-rank q-ary lattice admitting the qualifying prefix. For terminal blocks a finite modular ensemble requires its own marked counts. The Haar identity comes from continuous invariance, absent for fixed modulus, and its first-moment obstruction at $X_G$ supplies neither a modular failure rate nor a failure rate for the actual BKZ selection. A simultaneous terminal probability proof at that cutoff would have to control the existence of bad prefixes beyond their expected multiplicity.


## Independent audit (Nov 2026)

Verdict: **correct**; numerics reproduce (e.g. 141599.7 bits at `b = 400`). Framing caveat: the bound is driven almost
entirely by the prefix count `A·X_G^n` (`X_G` far above the typical minimal prefix determinant); the S1 factor subtracts only
≈ 465–2245 bits, so any shape event with probability above `2^{−143846}` gives the same conclusion. The interior-block
construction is deterministic but refutes only the quantifier with unrestricted continuation determinant.
