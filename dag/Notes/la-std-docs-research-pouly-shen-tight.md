---
title: "Fixed-instance concentration and geometry in Pouly–Shen"
refs: []
tags: [lattice-attack]
---
*Moved from `docs/research/pouly_shen_tight.md` (core v0.1.2).*

# Fixed-instance concentration and geometry in Pouly–Shen

The union in Lemma 7 serves a stronger conclusion than Algorithm 2 needs. Restricting it to the scores actually compared, then using an explicit one-sided Hoeffding bound and the available score gap, gives the following sensitivity at the **printed** Table 1 parameters. Each entry is a base-two logarithm of modeled work. Parentheses give the change from the preceding row. Equation (19) and the baseline script already use the secret dimension in the numerator of the sample count, so substituting the equation dimension there would exaggerate the savings. [Pouly–Shen, corrected version, §§4.2–4.4](https://eprint.iacr.org/2023/1508)

| Model or change | Kyber512 | Kyber768 | Kyber1024 |
|---|---:|---:|---:|
| Published Table 1 | 238 | 347 | 478 |
| Repository formula at printed parameters | 237.980 | 347.599 | 478.360 |
| 1. Candidate count, baseline normalization | 237.475 (−0.505) | 345.471 (−2.128) | 478.328 (−0.032) |
| 2. Sharper geometric certificate, same width and tolerance | 237.475 (0) | 345.471 (0) | 478.328 (0) |
| 3. Explicit sample bound using the gap | 237.451 (−0.023) | 345.267 (−0.205) | 478.327 (−0.001) |
| 4. Illustrative polynomial accounting | 247.771 (+10.319) | 360.546 (+15.279) | 487.292 (+8.965) |

Reproduce with `python python/pouly_shen_tight.py`. The script reuses the baseline BKZ, GSA and Gaussian-mass approximations. Rows 1–3 hold the printed dimensions, block size and width fixed. Row 1 isolates the numerator substitution from the changes to confidence and tolerance in row 3. Row 4 counts selected primitives under stated prices. No row measures an implementation. The matrix model assumes access to the listed 1023/1519/2025 equations. The geometric inputs in the calculation are heuristic.

## 1. A finite set fixed before sampling

Condition on the matrix, secret and error. Put $D=L_q(A_{dual})$, $g=n_{guess}$ and $K=q^g$. Modulo $D$, every score is evaluated at $e+A_{guess}v$ for some $v$ in the guessed block, including zero. The exact mean and each sample cosine are $D$-periodic by duality. Thus at most $K$ points matter. Full column rank over the Kyber field ensures distinct cosets. Lemma 7's uniform statement on all integer points still has its original quantifiers. For general Lemma 9 the count is the index $[L:L\cap D]$.

Each cosine has range $[-1,1]$. For independent draws, Hoeffding bounds either specified one-sided deviation of its average by $\exp(-N\delta^2/2)$. Count a downward deviation for the correct score and an upward deviation for each competitor. A union gives $K\exp(-N\delta^2/2)$, allowing arbitrary dependence among candidate scores. Row 1 alone replaces $n\ln q$ by $g\ln q$ in the baseline $N$.

## 2. Relaxing the shortest-vector test

Let $d$ lower-bound the distance from every wrong query to $D$. One admissible choice is $d=\lambda_1(L_q(A))-\|e\|$. A stronger choice is the actual minimum wrong-query distance. Indeed every nonzero guessed shift represents a coset disjoint from $D$. Consequently one can also replace the first minimum by the minimum norm in $L_q(A)\setminus D$ before subtracting $\|e\|$. Short vectors inside $D$ impose no obstruction in this argument.

Write $a=1/s$, $r=\|e\|$, $\tau=a\sqrt{m/(2\pi)}$ and $u=(d/\tau)^2$ for $d\ge0$. For $u>1$ the wrong mean is bounded by
$$ B=\exp[(m/2)(1+\ln u-u)]. $$
For $d\le\tau$ use $B=1$. To prove the bound, split the exponent of every Gaussian term on $D-x$ into fractions $1-t$ and $t$, with $0<t\le1$. Extract $\exp[-\pi(1-t)d^2/a^2]$ and sum the remaining wider Gaussian. Poisson summation bounds its shifted mass by its unshifted mass (all Fourier coefficients are positive). The wider unshifted mass divided by the original mass is at most $t^{-m/2}$, since the dual Gaussian sum decreases when the primal width increases. Minimizing the product gives $t=1/u$ when $u>1$. Relative to Lemma 8's $\exp[-(m/2)(\sqrt u-1)^2]$, the log ratio is $m(1+\ln\sqrt u-\sqrt u)<0$.

Lemma 8 gives correct mean at least $P=\exp(-\pi s^2r^2)$. The sharp-tail sufficient test is $B<P-2\delta$ for the published strict-gap convention. This weakens the required distance for a given positive tolerance. Its dimension-only branch still needs $d>\tau$ to say anything. Applied with actual coset distances it dispenses with the global shortest-vector test. For the table only, substitute $r=\sqrt{m\eta/2}$ and $\lambda=\sqrt{m/(2\pi\mathrm e)}q^{1-n/m}$, as in the baseline. The resulting $\ln(B/P)$ values are −2560, −6118 and −8140. Geometry changes admissibility immediately but changes cost only when a cost input changes. These substitutions supply neither a per-key certificate nor a probability over Kyber keys.

The revised Qu–Xu abstract reports no estimated saving from modulus switching at the updated parameters. Qu–Tian–Wang–Xu combine a refined inequality with projected sampling, so their reported 26.1–45.8 bits cannot be attributed to the tail substitution here. [Qu–Xu](https://eprint.iacr.org/2025/859) and [Qu–Tian–Wang–Xu](https://eprint.iacr.org/2026/2117)

## 3. Choosing the tolerance

Set $G=P-B>0$. Taking bad deviations **at least** $G/2$ ensures strict score separation on the complementary event even at the midpoint tolerance. The correct empirical score is then positive as Algorithm 2 requires. With symmetric tolerances, $G/2$ is optimal for the common-deviation bound because its required sample count decreases with tolerance. For conditional failure at most $p$, take
$$ N=\left\lceil 2\ln(K/p)/(G/2)^2\right\rceil . $$
At $p=0.01$, the log sample counts are 122.980, 177.514 and 233.434, respectively. The cost calculation uses floating-point logs of the continuous counts. Rounding $N$ up and retaining $B$ in the exact formula have effects below the displayed precision. Row 3 is conditional on exact independent samples and exact score comparisons.

## 4. Explicit counts and unresolved prices

For independent restarted approximate draws take $\epsilon=0.01/N$. Coupling each with its ideal draw makes the joint discrepancy at most $N\epsilon=0.01$, giving total conditional failure at most 0.02. In Theorem 2 the multiplicative mixing penalty is **$1/\Delta$**. With uniform minorization $\Delta$, after $k$ steps the uncoupled mass is at most $(1-\Delta)^k\le e^{-k\Delta}$, hence $\lceil\ln(100N)/\Delta\rceil$ steps suffice. Equation (25) bounds the reciprocal from above given the actual Gram–Schmidt lengths. The script uses the baseline GSA approximation to that bound.

Here is one reproducible arithmetic convention for scoring. Form the $g+1$ projections onto the guessed columns and right-hand side, and accumulate the phase into one histogram bin. Allow $2m(g+1)+1$ arithmetic operations per draw, with a precomputed phase table. A direct length-$q$ transform along each of the $g$ axes uses at most $2qgK$ complex operations, followed by $K$ comparisons. This slower separable DFT makes its arithmetic count explicit. Row 4 prices each arithmetic operation, comparison and lookup-table phase access (folded into the histogram update) at unit or absorbed cost, uses $m^2$ units per MCMC step as in the baseline sensitivity, and neglects initialization and ceilings. Its total is BKZ plus sampling plus scoring.

An absolute bit-operation total is undetermined. Theorem 2 supplies no price for a one-dimensional Gaussian primitive at prescribed precision. The dense-update allowance omits that price, random bits, memory traffic, table construction and basis preprocessing. To certify rounded scores with worst-case error $h$ per normalized score, use a sampling tolerance at most $(G-2h)/2$ and prove the chosen arithmetic meets $h<G/2$. GSA and the MATZOV BKZ price also remain modeling assumptions. These missing implementation and instance inputs prevent turning row 4 into a certified Kyber security exponent.


## Independent audit (Nov 2026)

Verdict: **mathematics correct**, script reproduces the table. Restricting the union to the `q^{n_guess}` candidate scores
is valid (W depends only on `A_dual`; one-sided events, no independence between candidates needed); the Banaszczyk-type
tail `B = exp[(m/2)(1 + ln u − u)]` and the Hoeffding `N = 2 ln(K/p)/(G/2)²` are correct.
**Caveat that changes the headline:** row 3 raises the tolerance from `P/100` to about `P/2`, with `P` evaluated at the RMS
error norm, so its guarantee covers only keys with `‖e‖ ≤ r` (about half), whereas the baseline's `/100` slack covers
`‖e‖²` up to ≈ 2–2.5 standard deviations. Matching that coverage (r at the 99th percentile of `‖e‖²`) gives totals
237.481 / 345.931 / 478.345, i.e. savings ≈ **0.50 / 1.67 / 0.02 bits** (not 0.53 / 2.33 / 0.03). All savings are capped by the
BKZ cost floor at the fixed printed parameters (`s`, `β` not re-optimised).
