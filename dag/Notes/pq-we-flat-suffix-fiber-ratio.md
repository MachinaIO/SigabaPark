---
title: Removing hidden-matrix Gaussian weights from the descendant transcript test
refs: [definition:WE_CircuitSAT]
tags: [witness-encryption, reduction, preimage-sampling]
---

Fix a common context in the descendant-preimage likelihood calculation,
including the same known block B of each preimage matrix A=[H|B] in
both worlds. H may vary across the affine hidden-state fiber. Suppose the
ambient column sampler before conditioning on its syndrome has independent
left and right coordinates. If the syndrome law of B on its own right
coordinates has mass in (1 +/- e)/Q everywhere, Q the syndrome group
size, then A has the same bound for every H simultaneously. Its law is
the convolution of B's law with a probability distribution. This applies
pointwise to an arbitrary target and any affine constraints on H. Use
the actual sampler's coordinates; conditioning on a previously revealed
right-coordinate vector destroys the independent smoothing block.

**Rank statistic.** Let N_i(t) count all compatible hidden states for
transcript t in world i, assuming a shared uniform affine prior of the
same size, common ambient sampler masses, and the hypotheses above for
each of J emitted columns. On good contexts with e<1 write
D=((1+e)/(1-e))^J. Wherever N_0>0 the exact likelihood ratio p_1/p_0
is between (N_1/N_0)/D and D(N_1/N_0), since every term in the fiber
sum has the same multiplicative envelope. In particular the ratio is
zero if N_1=0. Put S=E_0[min(1,N_1(t)/N_0(t))]. For the conditional
transcript laws,

    S/D <= 1-TV(p_0,p_1) <= min(1,D S).

This uses overlap as an expectation under just one world. It eliminates
the need to count a nonlinear subset of good hidden states *inside each
fiber*: goodness here depends only on the fixed smoothing blocks.
Modular linear solving gives N_i in polynomial bit complexity when all
retained constraints have the specified affine form. This statistic may
be evaluated on sampled transcripts if those and the common context can
be sampled; polynomially many trials do not certify negligible tails.
For example, if N_1>=N_0 except on world-0 mass beta on good contexts,
then TV is at most gamma+1-(1-beta)/D after averaging, where gamma bounds
the common prior probability of bad contexts. Other sampler errors add
separately. Dropping a common context after this comparison cannot
increase TV. Conversely a mismatch in an augmented context need not be
visible in the published ciphertext.

**Getting small e.** At dyadic q=2^k, k>=2, take a uniform B with n rows
and m_B>=2nk columns and centered discrete Gaussian width s>=8. The
syndrome-cap estimate gives E[max_y |Q Pr[BX=y|B]-1|] <= 2^(1-n(k-1)).
Indeed order-two characters contribute at most 2^n(5/8)^m_B and higher
orders at most Q(3/8)^m_B; averaging their nonnegative Fourier weights
gives the bound. Markov and union bound over L distinct blocks give
gamma <= L 2^(1-n(k-1))/e. Add each block's marginal distance from
uniform if necessary. Independence between blocks is unnecessary.
For n=32, k=16, m_B>=1024, e=2^-160, L<=2^16 and J<=2^24,
gamma<=2^-303 and, if beta=0, 1-1/D <= 2Je/(1+e) < 2^-135.
This is a numerical sufficient regime for the normalization error only.

**Application to the Bonsai split.** The trapdoor-generated second block
in PR 111 is a natural candidate to condition on if its marginal is close
to uniform and its width satisfies the estimate. In the ideal full
preimage law this conditions on the *matrix*, not on the sampled portion
of the preimage. If that portion is also constrained by the challenge,
one must check which coordinates remain fresh in the conditional sampler
and use the corresponding B. Most importantly, the actual frontier
still needs a bound on the unweighted rank statistic (or its failure
probability beta) with all branches, payload and later uses present.
Flat syndrome masses alone do not prove that comparison.
