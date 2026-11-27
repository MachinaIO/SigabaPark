---
title: Short error laws invariant under shared-cover slot swaps
refs: [definition:WE_CircuitSAT]
tags: [witness-encryption, reduction, error-distribution]
---

In section 5 of [the APG-direct frontier note](https://github.com/MachinaIO/SigabaPark/blob/31e08b3294d55b083b8c1038491cb6847087a755/dag/Notes/pq-we-point-insertion-frontier.md),
a swap is expressed in coordinates g=d+w c and h=w c, w in {1,-1}.
In original coordinates it acts by T(d,c)=(-d,c+w d).
Left-multiplying both a preimage constraint matrix A and its target Y by
an invertible T preserves the set of D solving AD=Y exactly. If D is
sampled by a fixed law depending only on that set, this also preserves its
conditional distribution. Making the *distribution of the target errors*
equivariant is a separate issue. The following is a modified error design,
not an assertion that the errors in the PR need to be changed for its SCC.

**Many sources, one cover.** Take free slots i with fixed signs w_i and
one cover c. Sample independent short blocks U_i,V_i,Z with U_i,V_i
identically distributed. Use E_i=U_i-V_i and E_c=Z+sum_i w_i V_i.
Swapping U_i with V_i negates E_i and adds w_i E_i to E_c, leaving
other free slots unchanged. Thus one error distribution is exactly
invariant under all these cover swaps, without sampling the group orbit.
For centered inputs with coordinate variance sigma^2, free variance is
2 sigma^2 and cover variance is (k+1)sigma^2 for k free slots. If input
coordinates have absolute bound B, the respective deterministic bounds
are 2B and (k+1)B. Charge the cover growth in any decoding margin.

The law can be added to an independent-error challenge at this interface.
Use baseline errors (U_1,...,U_k,Z) from that challenge and add the
independently sampled vector (-V_1,...,-V_k,sum w_i V_i) to its targets.
Uniform independent ideal targets remain uniform after this addition.
This is efficient postprocessing of a joint challenge with accessible
targets. If other public data, such as already sampled preimages, are
conditioned on the original targets, shifting targets alone does not
update those data. Sampling the right preimages and preserving the root
row jointly still have to be proved in the full scheme.

**One source, two covers.** Suppose instead an error law on (d,c1,c2)
must be invariant under the two individual swaps with distinct covers
and unit signs. Composing them translates the cover coordinates by
(w1 d,-w2 d) while fixing d (up to reversing the order). For a prime
modulus q, condition on any nonzero d. Iterating gives a full q-cycle
on c1, so exact invariance forces c1 uniform mod q in this slice.
In particular, with nonzero d of probability p, the unconditional
probability of |c1|>B in centered representatives is at least
p(1-(2B+1)/q) when 2B+1<=q. This is incompatible with substantial p
and tight deterministic noise bounds. For block-valued errors the same
claim applies to a coordinate with nonzero d at that coordinate.

Quantitatively, if the total variation distance under each swap is at
most epsilon, it is at most 2j epsilon under j compositions of the pair.
Averaging the translated laws over j=0,...,q-1 gives distance at most
(q-1)epsilon from the original and a uniform c1 marginal conditional
on nonzero d. Subtract (q-1)epsilon from the tail bound above. The
estimate is meaningful only at the corresponding modulus and error scale.
This rules out one common short error law for competing exact symmetries
in this template; it leaves open changing the law between hybrids or using
computational hiding. Neither the non-co-located frontier flip nor the
dead-chain lengthening follows just from shared-cover error symmetry.
