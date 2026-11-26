---
title: Planting binary-prefix lifts in a uniform matrix extension with an exposed root row
refs: [definition:WE_CircuitSAT]
tags: [witness-encryption, reduction, preimage-sampling]
---

At the single matrix interface of the prefix-carry transport, suppose
the reduction receives a uniform A0 in (Z/q)^(n by m) and may generate
r additional columns. Other challenge data Z may depend on A0. Before
sampling any hidden lifts, fix a computable update delta and projection
P using A0,Z and independent coins. Let D contain the binary-prefix
multiples n_i delta. Draw each t_i independently and uniformly from
the m-bit strings of Hamming weight k. Publish A=[A0 | D-A0 T] with
T formed from the t_i. Retain v_i=(t_i,e_i) privately. They are linearly
independent, of norm exactly sqrt(k+1), and A v_i=n_i delta. This is a
restricted gadget programming interface in the style of
[Micciancio and Peikert](https://doi.org/10.1007/978-3-642-29011-4_41).

**Joint distribution.** Let M=binomial(m,k), Q=q^n. The TV distance
of (Z,A,P A) from replacing the appended block by independent uniform
columns and computing the same root is at most sqrt(r (Q-1)/(2M)).
Indeed, for fixed A0 let H be the law of A0 t. Distinct binary t have
a unit difference in some coordinate even at composite q. Under uniform
A0 their hashes collide with probability 1/Q. Thus the expected
chi-square divergence from uniform is (Q-1)/M, including the contribution
of identical inputs. In natural logarithms KL(H||uniform) is at most
that chi-square divergence. Conditional on A0,Z,P,D the appended columns
are independent translated negatives of H. Their KL divergences add.
Averaging and applying Pinsker gives the claimed joint bound, even for
shifts depending on A0,Z. Finally P A is a deterministic postprocessing
given P,A. The claim also holds with P,D included on both sides when
they were fixed as stated. It is an average over the challenge matrix,
not a worst-case extractor bound for each fixed A0.

**What the exposed root constrains.** Publishing R=P A creates no extra
distance in this lemma. If the experiment also requires R X to stay
fixed for the preimage X during a syndrome change, the identity
R(X'-X)=P delta is necessary; when P delta=0 it holds for every valid
transport. This extra condition applies only when that reading is retained.
A separate independent uniform block of root constraints may instead be
incorporated in A0 as extra rows with zero target displacement; pay for
their dimension in Q. An arbitrary previously fixed correlated root is
not covered by treating it as fresh uniform rows.

**Combination.** For h delta=0, r=floor(log2 h), the prefix-carry
sampler can now use L=sqrt(k+1) provided the source preimage conditional
on the matrix, retained view and T has the specified coset Gaussian law.
If its transport error is eta for every such context, compare first to
an ideal destination sampler conditional on the context. If the ideal
sampler uses only public/interface data, discard T and switch to uniform
columns at the displayed distance. This order matters: exposing T itself
or generating later public objects directly from T is not covered by the
matrix replacement bound.

For an illustrative interface n=256, q=h=65536, m=8192 and r=16, the
smallest k satisfying binomial(m,k)>=r Q 2^256 is 992. The resulting
lift norm is sqrt(993), and the joint matrix distance is below 2^-128.
These are illustrative matrix dimensions and do not constitute a decoding
margin or a hardness estimate. The construction needs r programmable
columns, the public target update or its prefix multiples, and a valid
conditional preimage. The fixed challenge in APG-direct has not been
shown to supply these without disturbing the level preimages, other
target blocks or their correlations. The lemma does not establish PI.
