---
title: Conditional rank of an unchanged preimage branch and the directions left to its parent
refs: [definition:WE_CircuitSAT]
tags: [witness-encryption, reduction, preimage-sampling]
---

Fix q=p^k, a prime power, and an n by m matrix A of full row rank mod p.
Suppose the unchanged branch publishes m integer preimage columns D with
AD=Y mod q. Write bars for reduction mod p, t=rank(Ybar), and d=m-n.
Do not model Dbar as uniform over all matrices: the syndromes constrain
each column. In the model of independent *uniform compatible residues*,
the exact rank law is

    rank(Dbar) = in distribution t + rank(U),
    U uniform of shape d by (m-t) over F_p.

Indeed an invertible ambient basis change makes Abar=[I 0], so the fixed
top rows of Dbar are Ybar and the bottom rows form an independent uniform
matrix. Mod out by the row span of Ybar. The residual bottom rows are
uniform in dimension m-t, proving the formula.

If t=n, D is invertible modulo q with probability
product_{j=1}^d(1-p^(-j)). For p=2 this is at least 9/32 for d>=2:
the first two factors give 3/8 and the remaining product is at least
1-sum_{j>=3}2^(-j)=3/4. For d=0,1 the probability is larger.
Thus parent-only movement preserving this branch is identically zero
on a constant fraction of transcripts under the stated law, even with
arbitrary downstream freedom held fixed. This obstructs a nonzero
parent-only update on such transcripts; it is not a distinguishing test
between APG programs.

If t<n put g=n-t. Except with probability at most
(p^d-1) p^(-(m-t)) < p^(-g) (union over nonzero row combinations),
U has full row rank. In this case the entire *mod-p* left kernel of
Dbar is exactly {z Abar : z Ybar=0}. Inclusion follows from AD=Y,
and equality by dimension g and the injectivity of z -> z Abar.
Thus even when the unchanged branch is singular the available parent
directions mod p can come entirely from syndrome relations. This
description does not automatically lift to the kernel mod p^k.

**When uniform compatible residues are justified.** For fixed y, in
the full coset Ax=y mod q every mod-p residue satisfying Abar r=ybar is
attainable: put x=r+p z and solve A z=(y-Ar)/p mod q/p, possible by
surjectivity. Each residue class in the coset is a translate of the
same lattice K=p {z:Az=0 mod q/p}. Suppose the centered width-s
Gaussian masses of these translates all lie within (1 +/- e) of a
common positive mass, e<1. Normalization then puts the residue law at
TV distance at most e/(1-e) from uniform on compatible residues.
A sufficient smoothing condition is that the nonzero dual Gaussian
sum on K^* with weights exp(-pi s^2 ||w||^2) is at most e, by Poisson
summation. This is a condition on the finer residue fibers; flattening
only the original syndrome masses does not prove it. For m conditionally
independent columns, subtract at most m e/(1-e) from the asserted
success probabilities, plus any sampler or bad-context error. Require
this law conditional on the retained data used in the argument.
The actual frontier still needs a proof of this flatness at its sampling
width and a distributional bound for t. There is no unconditional
constant-probability assertion here for its sampled D.
