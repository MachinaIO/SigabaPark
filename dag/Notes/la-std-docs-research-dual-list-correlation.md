---
title: "Correlations in a complete dual shell"
refs: []
tags: [lattice-attack]
---
*Moved from `docs/research/dual_list_correlation.md` (core v0.1.2).*

# Correlations in a complete dual shell

A complete shell can have quadratic score variance even after choosing one representative from each antipodal pair. The uniform-input second moment, in contrast, is determined exactly by residue collisions. These statements concern a fixed lattice and randomness in a common input. Pouly–Shen Theorem 6 fixes the input and takes probability over the sampled list. The distinction matters even if list indices are sampled independently. [Pouly–Shen, Lemma 9 and Theorem 6](https://eprint.iacr.org/2023/1508)

## A deterministic shell bound

Let the list consist of the integer points of a lattice in a specified ball or shell, with any stated convention on zero and signs. Enumeration here means the complete finite set. Applying a complete-ball model to an actual sieve requires a separate justification. Reduce the list modulo an integer $q>1$ and retain multiplicities. For $X$ of law $P$ on $(\mathbb Z/q)^d$, put $h(t)=E_P\cos(2\pi\langle t,X\rangle/q)$, $C_j=\cos(2\pi\langle w_j,X\rangle/q)$ and $S=\sum_j C_j$. Write $D=N(N-1)$ for a list of size $N$. Define $a(t)$ as half the total number of occurrences of $t$ among the sums and differences $w_j\pm w_k$ for ordered pairs $j\ne k$. Both signs count even if they coincide modulo $q$. Then

$$
 B_P=\sum_{j\ne k} E_P C_j C_k=\sum_t a(t)h(t),\qquad
 |B_P-a(0)|\le (D-a(0))\epsilon,
$$

where $\epsilon$ is the maximum of $|h(t)|$ over occupied nonzero bins (zero for an empty set). Indeed the cosine product identity gives the equality term by term, $h(0)=1$, and the total bin weight is $D$. For uniform input all nonzero coefficients vanish by character orthogonality (translate the sum by a coordinate vector on which the character is nontrivial). Thus $B_U=a(0)$ exactly. For a sign-symmetric shell with distinct nonzero residues, none self-inverse, each vector has one negative partner and no other collision. Hence $B_U=N/2$ and $\operatorname{Var}_U S=N$, including the $N/2$ diagonal contribution. For general $P$ the exact centered variance is

$$
 v_P=B_P+\tfrac12\sum_j(1+h(2w_j))-
          \left(\sum_j h(w_j)\right)^2.
$$

This follows by squaring $S$ and using the double-angle identity. A large uncentered cross term alone need not imply a large variance.

## What subset selection changes

Choose a uniform size-$k$ subset independently of $X$, with $2\le k\le N$. Each distinct ordered pair is included with probability $k(k-1)/D$ by symmetry and counting included pairs. The expected off-diagonal sum therefore equals $k(k-1)B_P/D$ exactly. In particular the average contribution per ordered pair survives thinning. Independent random signs preserve every cosine pointwise. For independent draws of indices with replacement write $M(X)=S(X)/N$. Given $X$, the sampled cosines are independent with conditional mean $M(X)$. Their unconditional covariance for distinct draw positions is exactly $\operatorname{Var}_P M(X)$ by iterated expectation. These identities require no sieve heuristic.

## A sufficient decision criterion

For two input laws $P,U$ on the same fixed list, let $g=E_P S-E_U S>0$. Accept $P$ above the midpoint of the means. Under either law an error requires a deviation of magnitude at least $g/2$. Applying Markov's inequality to each squared deviation bounds the sum of error probabilities by $4(v_P+v_U)/g^2$. Consequently $v_P+v_U\le g^2/16$ suffices for acceptance-probability difference at least $3/4$. All quantities have exact finite expressions above. This criterion is conditional on a verified gap and variances. It concerns binary decision on fresh inputs. Recovering a guessed block with high probability over lists, as in Theorem 6, additionally entails controlling the competing scores in that experiment.

## Counterexample without modular collisions

Take $q=4$ and the complete unit shell of $\mathbb Z^d$, namely $\{\pm e_i\}$. With equal probabilities choose $X=0$ or $X=(2,\ldots,2)$. Every cosine equals the same fair sign, so $B_P=D$ and $v_P=N^2$. The calculation still holds after retaining just the positive axes, with $N=d$, or after choosing any fixed-size subset independently. Already in dimension two the two positive directions are distinct modulo sign and give variance four. Even a positive distinguishing advantage can fail for the complete shell. In dimension two compare uniform input modulo four with $(Y,Y)$ for uniform $Y$ modulo four. These particular laws have equal score means but different score distributions. For an example with *identical* score distributions, take uniform independent coordinates $(Y,Z)$ and replace each by its representative in $\{0,1,2\}$ under negation (map 3 to 1). The laws differ, yet all four unit-shell cosines agree under this coupling, hence every decision based only on the score has advantage zero.

## Scope of the published results

Ducas–Pulles distinguish unconditional contradictions in some regimes from contradictions with established heuristics in the regimes used for concrete estimates. Pouly–Shen §6.1, Eq. (29), expresses the comparison as $T^{-1/m}\operatorname{GH}(L_q(A_{\rm dual}))<\sqrt{m/(2\pi)}\,\sigma_e$. The left side uses the Gaussian-heuristic length and the number $T$ of targets. Replacing it by the exact first minimum, or dropping the target factor, changes the condition. Theorem 6 itself requires an exact minimum-distance and Gaussian-weight gap for the full primal lattice. Section 6.2 also distinguishes the target distributions. [Ducas–Pulles, CRYPTO 2023](https://eprint.iacr.org/2023/302) and [Pouly–Shen, §6](https://eprint.iacr.org/2023/1508)

The later Ducas–Pulles prediction conditions on error length, models sieve vectors as uniform in a ball, and approximates the Voronoi cell by a ball for incorrect candidates. These are modeling assumptions. Laarhoven (claimed, not verified here; arXiv 2609.37483 per the literature survey — distinct from the Doulgerakis–Laarhoven arXiv:2609.37482 cited in PROOF_GAP for assumption (B)) states an asymptotic decision result for complete dual balls in the Haar-random lattice model using Siegel and Rogers moments, with a prescribed planted radius and a uniform target modulo the lattice. The lattice ensemble is part of that theorem. Transferring it to a fixed q-ary lattice and the incomplete list returned by a particular sieve would require control of that list and its input law. No such transfer or concrete security estimate follows here. [Ducas–Pulles, score prediction](https://eprint.iacr.org/2023/1850) and [Laarhoven, Haar-random lattice result](https://arxiv.org/abs/2609.37483)


## Independent audit (Nov 2026)

Verdict: **correct** (exact Fraction checks with q = 4, 6). Notes: `a(0)` is a half-weighted count (a pair with both
`w_j ≡ w_k` and `w_j ≡ −w_k` scores 1); the `(Y,Y)` example defeats only the mean/midpoint test (a test on `|S| = 4`
still distinguishes) — the claim that even a positive advantage can vanish is supported by the folded example, which is
trivial (an even score cannot separate `x` from `−x`); Cantelli would slightly tighten the midpoint bound. The Laarhoven
citation is unverified.
