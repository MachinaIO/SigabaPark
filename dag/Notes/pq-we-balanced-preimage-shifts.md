---
title: Transporting a centered Gaussian preimage to a shifted syndrome by balanced lifts
refs: [definition:WE_CircuitSAT]
tags: [witness-encryption, reduction, preimage-sampling]
---

A change in a masked target is insufficient unless the reduction also
updates its published preimage. Here is a conditional transport at the
ideal coset-sampler interface. Fix public auxiliary data, a matrix A mod q,
and an original syndrome y. Let C0={x in Z^m: Ax=y}, C1={x: Ax=y+delta}.
Take rho(x)=exp(-pi ||x||^2/s^2), Zi=sum_{Ci}rho. Assume fresh independent
samples from rho/Z0 on C0 *at this same fixed auxiliary view*. Supply an
efficiently enumerable finite distribution on integer lifts V satisfying
AV=delta for every lift and E[V]=0 over the reals. Write
alpha=pi E[||V||^2]/s^2. The construction adapts the bimodal rejection idea
of [Ducas et al.](https://eprint.iacr.org/2013/383.pdf).

Draw X from C0 and independent V. Propose z=X+V. Its mass on C1 is
rho(z) H(z)/Z0, where

    H(z) = E_V exp((2 pi <z,V> - pi ||V||^2)/s^2).

By Jensen and real centering, H(z)>=exp(-alpha) for every z. Accept with
probability exp(-alpha)/H(z). The accepted mass is proportional to rho
on C1, with success probability exp(-alpha) Z1/Z0. Applying the same
proposal calculation to -V in reverse gives Z0/Z1>=exp(-alpha); the
forward proposal gives Z1/Z0>=exp(-alpha). Hence success is at least
exp(-2alpha) without a smoothing-parameter assumption. Independent
conditional retries have expected count at most exp(2alpha). Capping at
K proposals gives failure at most exp(-K exp(-2alpha)). These statements
are exact for ideal sampling and real acceptance coins. A concrete PPT
implementation must charge finite precision, finite tails and its cap.

**Short lifts.** For 2 delta=0 and Av=delta take fair V in {v,-v}.
Acceptance reduces to 1/cosh(2 pi <z,v>/s^2). For order h>=2 take v with
probability (h-1)/h and -(h-1)v otherwise. Their mean vanishes and both
have the required syndrome; E||V||^2=(h-1)||v||^2. Thus higher order is
possible, but this particular lift distribution may be too expensive.
Extra linear conditions B X=b exposed in the view can be handled by
stacking B below A and requiring BV=0 modulo the corresponding modulus.
Flatten a matrix preimage for joint shifts with Frobenius norm, or process
columns separately only if the required conditional distribution factors.

**Application boundary.** Retrying with the same X and new signs conditions
on X and generally biases the output. A simulator holding just one
preimage can use a single attempt with abort, but success depends on y
through Z1/Z0; conditioning on success can change the auxiliary-view
marginal. Conditional retries using fresh source samples keep a previously
sampled public root row fixed. If the root and preimage have dependencies
beyond the imposed affine conditions, the source oracle must sample the
true conditional law. For the APG-direct frontier this leaves two explicit
obligations: exhibit balanced short lifts for the actual change of target
(not merely a change of decoded bit), and implement enough conditional
samples in the fixed-challenge simulation. The lemma does not grant a
trapdoor or supply either obligation.
