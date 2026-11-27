---
title: Single-preimage syndrome transport by resampling along one short direction
refs: [definition:WE_CircuitSAT]
tags: [witness-encryption, reduction, preimage-sampling]
---

Fix auxiliary data including A,y. Let X have centered Gaussian mass
rho(x)=exp(-pi ||x||^2/s^2) on C0={x:Ax=y mod q}. Given a nonzero
integer v with Av=delta, let h>=1 satisfy h delta=0. Put u=h v and
tau=s/||u||. One source sample suffices under a one-dimensional smoothing
condition. No independent source-coset retry is needed.

Set z0=X+v and sample an integer j with weight proportional to
exp(-pi (j+<z0,u>/||u||^2)^2/tau^2). Output z=z0+j u.
Its syndrome is y+delta. Partition C0 by translates of Z u; addition
of v bijects these discrete lines with the corresponding partition of
C1={z:Az=y+delta}. On a destination line the procedure samples precisely
the target conditional distribution, independently of which representative
X on the source line was obtained. Only the distribution of line labels
can differ. In particular the TV distance is exactly the TV distance of
the source and destination line marginals under this bijection.

For a representative t the line mass factors into rho(t_perp) times
sum_j exp(-pi(j+<t,u>/||u||^2)^2/tau^2), where t_perp is its projection
orthogonal to u. Corresponding lines have the same projection since v
is parallel to u; distinct line labels may share that projection.
One-dimensional Poisson summation puts the sum in tau(1 +/- epsilon)
uniformly over its center, with epsilon <= 2r/(1-r),
r=exp(-pi tau^2), by summing the nonzero Fourier terms.
Each normalized line law is within epsilon/(1-epsilon) in TV of the
common reference distribution on labels proportional to rho(t_perp):
its likelihood ratio is in [(1-epsilon)/(1+epsilon),
(1+epsilon)/(1-epsilon)]. Thus transport error is at most
2epsilon/(1-epsilon) for epsilon<1. This is the shifted-Gaussian mass
estimate applied in just one dimension.
[Micciancio and Regev](https://cims.nyu.edu/~regev/papers/average.pdf)

For lambda>=1, taking tau >= sqrt((lambda+4) ln(2)/pi) gives error
below 2^-lambda. At lambda=128 and h=2 the sufficient s/||v|| is
about 10.8. An implementation with a scalar sampler at TV error eta
adds at most eta. For polynomial tau one explicit bounded implementation
rounds the center to its nearest integer, enumerates an interval of
radius O(1+tau sqrt(lambda+log(2+tau))) around it, and samples to
sufficient absolute precision from the normalized weights. The Gaussian
tail and accumulated rounding errors must be included for the chosen
cutoff. There is no matrix-dimension multiplier in the ideal line bound.

**What is preserved.** Linear auxiliary observations of the preimage are
unchanged if v belongs to their modular kernel. More generally the argument
is conditional on X having the stated source law given every retained
public value, and on v fixed given that context, independently of X. If
that law is only xi-close, data processing adds xi. Uniform conditional
bounds average over a retained random root without abort bias. The source
preimage must be replaceable: a second visible copy of X creates a joint
constraint outside this claim. The proof still needs a short lift of the
actual target update in the APG encoding and a decoding-compatible width;
a short lift of a downstream plaintext difference alone is insufficient.
