---
title: A modular shear certificate for equal point-insertion transcript counts
refs: [definition:WE_CircuitSAT]
tags: [witness-encryption, reduction, linear-algebra]
---

Fix the full integer preimage transcript, transitions and error coins as in
the descendant-fiber calculation. Vectorize the common hidden variables a
over R=Z/q. The common linear constraints are J a=j. Suppose the old
remaining target is L a and the new one is L a+U(V a+b), with the same
required right side. U has r columns. Find a lift matrix Q satisfying

    J Q=0,   L Q=U,   I_r+V Q invertible over R.

Then a -> a+Q(V a+b) maps new solutions bijectively to old ones. The
common equations stay fixed and the old target of the image is the new
target of the source. Given the image y, recover the source as
y-Q(I_r+VQ)^(-1)(Vy+b). This is an affine permutation on the full
ambient module, including when q is composite. Q may depend on the
public transcript when used for counting. It need not be a short lift:
this is a permutation of uniform modular latent states. With Gaussian
preimage columns their relative weights still require the previously
stated flat-mass condition; the shear alone does not preserve them.
One can test the certificate on any proposed restricted support for Q by
including equations setting all other rows to zero.

**Complete rank-one lift test for this certificate.** Solve Jk=0,Lk=u
for one k0. If insoluble this lift shape fails. Otherwise obtain generators
of N=ker[J;L] by Smith form. For the single row v=V, the scalar values vN
form the ideal gR, where g is the gcd of q and v applied to the generators
(g=q for zero image). Set d=1+v k0. Some lift yields an invertible scalar
iff gcd(d,g)=1. Necessity follows since all candidates are d modulo g.
For sufficiency, primes dividing g never divide any candidate. Let q'
be the largest divisor of q coprime to g, obtainable by repeatedly
dividing a working copy of q by its gcd with g until coprime. Select a
candidate equal to d modulo g and 1 modulo q' by CRT. It is a unit and
its difference from d is an attainable vN. Thus even at dyadic modulus
the test requires only modular solves and gcds. Failure rules out this
shear, not other equalities of fiber sizes.

**Which level can absorb the update?** In the branch equations
A_prev D_b=S_b A_next+E_b, take a flip affecting only b=1 and keep
A_next unchanged. If only A_prev may change, its increment H must
satisfy H D_0=0 and H D_1 equal the required target increment (up to
the direction of comparison), along with the other retained constraints.
In particular an invertible unchanged-branch D_0 over R forces H=0.
Over a field the stacked pair of right actions has precisely the range
obtained by choosing each row of H in the left kernel of D_0, then
multiplying by D_1. This gives an immediate support test for a proposed
parent-only lift before evaluating any smoothing bound. It makes no
claim about the probability of invertibility for the actual preimages.
Allowing both levels to change reopens directions but must preserve the
descendant equations in J. A single slot flip can affect many scalar
coordinates; the modular rank-one test only applies at r=1. No
full-transcript lift for the APG-direct non-co-located flip has yet
been exhibited.
