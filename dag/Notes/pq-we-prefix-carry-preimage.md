---
title: Transport with one source preimage and short lifts of the binary prefixes of the syndrome order
refs: [definition:WE_CircuitSAT]
tags: [witness-encryption, reduction, preimage-sampling]
---

Fix A,y and auxiliary data. The goal is to turn a centered width-s
Gaussian sample on Ax=y into one on Ax=y+delta. The earlier one-dimensional
line transport uses a kernel step of length h||v|| when Av=delta and
h delta=0. Here is a different sufficient interface, for any integer h>=2
annihilating delta. It trades that large width for additional short lifts.
The binary gadget and short-basis sampling background is in
[Micciancio and Peikert](https://web.eecs.umich.edu/~cpeikert/pubs/efftrap.pdf).

Read h in binary, starting at n_0=1 and successively forming
n_(i+1)=2 n_i+b_i until n_r=h, where r=floor(log2 h).
Supply independent-over-the-reals integer columns v_0,...,v_(r-1)
with A v_i=n_i delta and ||v_i||<=L. Put v_r=0. For i=0,...,r-1 form

    u_i = 2 v_i + b_i v_0 - v_(i+1).

These columns have zero syndrome and norm at most 4L. They span the
same real space as the lifts: modulo their real span induction gives
v_i=n_i v_0, so h v_0=0 there. Consequently they are a basis for the
rank-r sublattice K they generate and v_0 belongs to its real span.
No basis for the ambient kernel is required. The binary prefixes avoid
a long final carry even for odd h. If auxiliary linear readings must stay
fixed, impose zero displacement in those readings on every supplied lift.

Partition each syndrome fiber into cosets of K. Addition of v_0 matches
the source cosets bijectively to the destination cosets, preserving the
orthogonal projection onto span(K)-perp. Given one source point X,
sample on X+v_0+K by reverse Gram-Schmidt Gaussian sampling: from the
last basis column to the first sample its integer coefficient with the
center that cancels the projection of the current offset onto the
Gram-Schmidt column, using width tau_i=s/||u_i*||. Add this multiple of
u_i to the current offset. Always return the resulting point.

**Error bound.** Write t=s/(4L), z=exp(-pi t^2), e=2z/(1-z)<1.
Every scalar Gaussian normalization lies between tau_i(1-e) and
tau_i(1+e), by one-dimensional Poisson summation, uniformly in its
center. The reverse sampler probability of a point w equals
rho_s(w)/rho_s(w_perp) divided by the product of these normalizations:
orthogonality decomposes the squared norm in the exponent. Summing the
probabilities bounds each coset mass divided by rho_s(w_perp) between
the products of the lower and upper normalizations. Their ratio is
D=((1+e)/(1-e))^r. Each of the two coset-label marginals has likelihood
ratio between 1/D and D against the common reference proportional to
rho_s(w_perp) on matched labels. Each approximate conditional sampler
has the same likelihood ratio bounds against its ideal coset Gaussian.
By the triangle inequality the total TV error is at most 3(D-1)/2.
This counts both label discrepancies and the scalar-sampling construction
inside the destination coset. Errors in finite-precision scalar samplers
add at most the sum of their per-step TV errors.

Thus s=O(L sqrt(lambda+log(2r))) suffices for error 2^-lambda with
suitable constants and only r scalar draws. The statement assumes the
source law conditional on the retained view and lift family is the
required Gaussian. A concrete way to realize the algebra in isolation
is to append columns n_i delta-Abar t_i to Abar and take v_i=(t_i,e_i)
with the identity-coordinate block. This gives independent lifts directly,
but the columns depend on the challenge update. Their joint law with the
public root, the other ciphertext blocks and the fixed-game challenge
must be established for a WE reduction. Width must also respect decryption
noise. No such programming argument or APG point insertion is proved here.
