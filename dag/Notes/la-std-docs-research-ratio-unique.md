---
title: "A unique short line in a fully block-reduced basis"
refs: []
tags: [lattice-attack]
---
*Moved from `docs/research/ratio_unique.md` (core v0.1.2).*

# A unique short line in a fully block-reduced basis

Let $2\le\beta\le d$, let $u$ be a primitive vector of a rank-$d$ Euclidean lattice $L$, and suppose every vector outside $\mathbb Zu$ has length strictly greater than $R>0$. Write $k=d-\beta$. With the constants of the [prefix ratio bound](wall1_prefix.md), every fully BKZ-$\beta$ reduced basis starts with $\pm u$ whenever
$$
\|u\|\le R\exp(-p_0^{(k)}).
$$
The weak inequality here suffices because the lower bound outside the line is strict.

## Monotonicity of the ratio bound

Translation of the recurrence gives $p_i^{(t)}=P_{t-i}$, where $P_0=0$ and $P_j$ is the minimum, over $2\le h\le\min(\beta,j+1)$, of
$$
A_h+\frac{P_{j-1}+\cdots+P_{j-h+1}}{h-1},
\qquad A_h=\frac{h c_h}{h-1}.
$$
For the chosen Hermite bounds, $A_h$ increases. For $2\le h\le8$ this follows by comparing $\log(\gamma_h^h)/(2(h-1))$ with the exact powers in the prefix note. For $h\ge9$ write $A_h=F(h)/(h-1)$ with $F(x)=x\log(2/\pi)/2+\log\Gamma(2+x/2)$. Log-convexity of Gamma makes the differences $F(h+1)-F(h)$ nondecreasing. The transition and base comparison are $A_8<0.397<0.453<A_9<0.454<0.480<A_{10}$, directly from the factorial and half-factorial values. The last comparison gives $F(10)-F(9)>A_9$. Since $A_{h+1}$ is the weighted average of $A_h$ and $F(h+1)-F(h)$ with weights $h-1$ and $1$, induction proves the assertion.

Now $P_1=A_2>0$. Assuming the profile has increased weakly through $j-1$, every previously available candidate at $j$ has a weakly larger moving average than at $j-1$. A newly available length $h=j+1$ averages $P_0,\ldots,P_{j-1}$. Compared with the old length $h-1$ at $j-1$, it adds the largest entry and increases the constant. Thus every candidate is at least $P_{j-1}$. This proves monotonicity even at the indices where the minimization domain grows.

## Proof

Let $\pi_i$ project orthogonally off the first $i$ basis vectors and put $g_i=\|\pi_i b_i\|$. The prefix ratio bound gives $g_i\ge g_0 e^{-P_i}$ for every $i$. Suppose $b_0$ lies outside $\mathbb Zu$, so $g_0>R$. Write $u=\sum a_j b_j$ with integral coefficients and let $t$ be the largest index with $a_t\ne0$.

If $t\ge k$, linear independence gives $\pi_k u\ne0$. The terminal block generates all of $\pi_k L$, and exact block reducedness makes $g_k$ its first minimum. Hence $\|u\|\ge\|\pi_k u\|\ge g_k>R e^{-P_k}$. If $t<k$, then $\pi_t u=a_t\pi_t b_t$, so $\|u\|\ge g_t>R e^{-P_t}\ge R e^{-P_k}$. Both cases contradict the hypothesis. Therefore $b_0$ is an integral multiple of $u$, and primitivity of the basis vector forces that multiple to be $\pm1$. This includes $k=0$. The only profile properties used are the pointwise ratio bound and $P_t\le P_k$ for $t<k$.

## Plain-LWE parameter calculation

Use $1\le m\le n$, $d=n+m+1$, $q=3329$, independent CBD coordinates with parameter $\eta$ for both error and secret, and an independent uniform plain matrix. For $u=(e,s,1)$ and $V_d$ the unit ball volume take the smaller of
$$
(2^{-64}q^m/V_d)^{1/d}-\sqrt d/2,\qquad
(1-10^{-50})q/\sqrt{1+\eta^2}.
$$
Discard nonpositive radii. The second expression enforces strict no-wrap. Conditional on any planting, the probability of a vector outside the line of length at most this radius is at most $2^{-64}$. [Volume theorem](../../SigabaNeoStd/Lattices/Planted/Volume.lean)

For a CBD coordinate $X$, set $M(z)=4^{-\eta}\sum_{j=-\eta}^\eta {2\eta\choose\eta+j}e^{zj^2}$. By exponential Markov and independence, the sum of the $d-1$ coordinate squares exceeds $C(z)=((d-1)\log M(z)+64\log 2)/z$ with probability at most $2^{-64}$ for each fixed $z>0$. Choose the best deterministic tilt among $0.01,0.02,\ldots,0.50$. Integrality gives the norm cutoff $U=\sqrt{1+\min((d-1)\eta^2,\lfloor\min_z C(z)\rfloor)}$. The two bounds together give success probability at least $1-2^{-63}$.

| Plain shape | $\eta$ | $m$ | $R$ | $U$ | Certified $\beta=d$ | 2016 + GSA $\beta$ | GSA with full RMS norm $\beta$ | Projection factor at 2016 comparison dimension |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| 512 | 3 | 188 | 39.99299 | 39.86226 | 701 | 406 | 460 | 1.588 |
| 768 | 2 | 248 | 37.65103 | 37.56328 | 1017 | 624 | 694 | 1.533 |
| 1024 | 2 | 326 | 42.73264 | 42.44997 | 1351 | 874 | 960 | 1.481 |

The certified column minimizes the strict test $U<R e^{-P_k}$ with these specific probability bounds. Dropping the cap $h\le\beta$ in the recurrence lowers the profile by induction and gives a lower bound on every feasible block size. For each sample count the script finds the largest offset passing this relaxed test. At the overall minimizing witness the cap admits all lengths through that offset, so the lower bound is attained. All three minima occur at exact full-dimensional reduction after sample optimization. The theorem certifies the output of a fully reduced basis. The cost of computing one remains open here. These probabilities describe the plain independent-matrix experiment.

The 2016 comparison uses the estimator's embedding scale $\tau=\sigma=\sqrt{\eta/2}$ and its dimension cap $2n$. Its GSA height is $\delta_\beta^{2\beta-d-1}(\sigma q^m)^{1/d}$. At fixed dimension, replacing the modeled projected RMS length $\sigma\sqrt\beta$ by $\sigma\sqrt d$ increases the threshold length by $\sqrt{d/\beta}$. Optimizing dimensions again yields the full-RMS column. The factors shown use dimensions 1024, 1467 and 1918 near the maximum projected-test margin at the first successful block size. At each certified witness the factor is exactly one. The GSA heights and RMS lengths are heuristic inputs, while the certificate uses a uniform ratio bound and a high-confidence ambient norm. [2016 projection estimate, §6.3](https://files.usenix.org/s3fs-public/cdn/sec16_paper_alkim.pdf) · [Estimator comparison](../PROOF_GAP.md)

Run `python python/ratio_unique.py` with mpmath installed. The certificate uses 70 decimal digits and the GSA comparison uses the repository's fixed-point root-Hermite factors. [Calculation](../../python/ratio_unique.py)

## Independent audit (Nov 2026)

Verdict: **correct**; every number reproduces and the bounds (R from `badMatrices_probability`, CBD
exponential-Markov tail) are rigorous; monotonicity of `p_0^{(t)}` checked by proof and numerically.
Caveat: the certified `β = d` is trivial — it is exact full-dimensional SVP under the unique-short-line event.
The ratio bound contributes nothing at the optimal `m` (gap `log(R/U) ≈ 0.003` nats vs the smallest step
`P_1 = 0.1438`); at `m = n` the gap is ≈ 2.2–2.5 nats, buying ≈ 35 offsets, i.e. `β ≈ d − 35 ≈ 990` for
n = 512, which is worse. The comparison with 406/624/874 is exact SVP in dimension d versus heuristic BKZ-β.
