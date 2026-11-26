---
title: Exact block shear completion for coupled frontier targets
refs: [definition:WE_CircuitSAT]
tags: [witness-encryption, reduction, linear-algebra]
---

Over R=Z/q the previous transcript-preserving shear requires JQ=0,
LQ=U and I_r+VQ invertible, where r columns encode the simultaneous
update. Testing r separate rank-one changes is insufficient. There is
a polynomial-time decision procedure for the entire block, including
composite q.

First solve JQ0=0, LQ0=U. On failure there is no such lift. Let N be a
generator matrix of the *modulo-q* common kernel of J,L from Smith form.
Every lift has form Q0+NX for unrestricted X. Write T=I+VQ0, W=VN.
There exists a valid shear exactly when the columns of [T W] generate
R^r. Thus a second Smith solve (whether [T W] has a right inverse)
decides existence without factoring q. It is important to compute N
before reduction modulo a prime: reducing J,L first may create kernel
directions that do not lift modulo q.

**Proof and construction.** Necessity follows from T+WX invertible.
For each prime p dividing q, full column span of [T W] mod p means
that T maps onto the quotient F_p^r/im(W). On the kernel K of that
quotient map, T takes values in im(W), and dim K=rank(W). Pick any
isomorphism K->im(W) and prescribe WX on K to equal that isomorphism
minus T. Extend by zero on a complement and solve for X over F_p.
Then T+WX is injective (any kernel vector first lies in K), hence
invertible. Choose the entries of X to match these residues for all p
by CRT. Its determinant test needs only mod p for each prime: a unit
mod every p dividing q is a unit mod q. This gives an explicit lift
for a supplied factorization, in particular using just F_2 for dyadic
q. If the span test fails, some prime admits a nonzero row annihilating
both T and W. It kills T+WX for every X. Local span suffices for global
span since the Smith invariant factors must then be units.

For any resulting Q the map a->a+Q(Va+b) preserves J and exactly
matches the old target at the image to the new target at the source.
The inverse uses (I+VQ)^(-1). This is a certificate for the unweighted
compatible-state counts conditional on a specified transcript. It still
requires control of preimage masses and of prior weights.

**A coupled two-level control.** Over F_2 take parent row x and child
row y of width two. Impose unchanged branch x I=y, and take the changed
branch from x D=e to x D=y+e (a scalar slot entry goes from zero to one),
where D has rows (0,1),(1,1). Both D and D-I are invertible. For every
observed row e the two systems each have one solution. Explicitly move
both rows by x_old=x_new (D-I) D^(-1) and y_old=x_old. This map is
an invertible block shear of the stated form: in column coordinates
take V to read minus the new child row transposed, U=I and Q stacking
two copies of (D^T)^(-1). Moving only the parent while keeping the
child fixed is impossible on the unchanged branch. A retained downstream
linear observation can matter even here: adding y=(1,0) and choosing
e=(1,0)D makes the old system consistent and the new one inconsistent.
This control matches the two branch equations at the linear interface;
its matrices are fixed toy observations, not samples from APG-direct.

As another check, two separate invertible coordinate shears can combine
into a singular update: over F_2 add row two to row one and simultaneously
row one to row two. Either addition alone is invertible; both outputs
together coincide. Block completion tests precisely this joint constraint.
The remaining security question is how frequently the full-transcript
test succeeds for the actual sampled descendants and frontier flip.
