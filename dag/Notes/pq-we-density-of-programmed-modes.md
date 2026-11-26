---
title: How frequently can public setup guesses statistically hide a false WE statement?
refs: [definition:WE_CircuitSAT]
tags: [witness-encryption, security-reduction, complexity]
---

Consider a proposed fixed-challenge reduction which programs a public mode
using a guess g. It suffices that a guess is good with inverse-polynomial
probability on each NO input, even when recognizing good guesses is hard,
for the following statistical-difference obstruction to apply. This
strengthens the single-public-mode diagnostic for this template.

Let x have length n. A uniform classical polynomial sampler draws g from
G(x), and two uniform classical circuits sample P(x,g,b) for b in {0,1}.
Write d(g) for their total variation distance. Suppose

* on YES inputs, E[d(g)] >= 1-e;
* on NO inputs, Pr[d(g) <= t] >= p.

Use worst-case bounds at length n, with an explicit polynomial upper bound
on 1/(p(1-t)). Define Q_b by emitting (g,P(x,g,b)). Its distance is exactly
E[d(g)] since different labels have disjoint support. This analytical
sampler may reveal g even when a ciphertext would keep it hidden. The
NO premise is therefore conditional on the chosen label. An unlabelled
mixture can cancel differences, so closeness of that mixture alone would
not justify the conditional bound.

Create two circuits S_b by sharing b as the parity of k uniform bits
subject to that parity, and independently running Q on each share, using
fresh labels each time. In signed-measure notation their difference is
2^(1-k) times (Q_0-Q_1) tensor-powered k times, by expansion. Taking the
half-L1 norm gives TV(S_0,S_1) = TV(Q_0,Q_1)^k exactly. Hence on YES the
distance is at least 1-ke, and on NO it is at most exp(-kp(1-t)). For
k >= ln(4)/(p(1-t)) and ke <= 1/4 this is a uniform reduction to Statistical
Difference with thresholds 1/4 and 3/4 (choose a computable polynomial k
satisfying both bounds). CircuitSAT in this template would put NP in SZK
by Sahai and Vadhan, *A Complete Problem for Statistical Zero Knowledge*,
https://www.cs.ucla.edu/~sahai/work/web/2003%20Publications/J.ACM2003.pdf .
The amplification is their XOR transformation applied to the labelled guess.
This is a conditional complexity consequence.

For a dual-mode WE application, verify the YES premise as follows. If a
fixed witness decrypts the candidate mode's two bit experiments with average
bit error eta over g and the uniform message, then E[d(g)] >= 1-2 eta.
A computational switch from correct real encryption yields this error
bound when an efficient reduction given the fixed challenge can sample the
corresponding view and test decryption success in both modes. Hardwiring
arbitrary (x,w) requires nonuniform hardness. The proof needs only average
success on YES, and needs no witness in the Statistical Difference circuits.

For instance, uniform guessing of a length-l advice string with even one
good string per false input gives p >= 2^(-l). At l <= c log2(n), constant
t bounded away from one and negligible e, the statistical test costs
O(n^c) sampler invocations. Long advice also meets the bound if good
strings have sufficient density. Superlogarithmic length alone does not
identify an escape. For a concrete design, measure density in the actual
efficient guess distribution and account for the conditional view after
revealing g. The lemma supplies no obstruction for sparse good guesses
through this bound, or for reductions with a purely computational terminal
comparison. Neither case supplies a WE construction by itself.
