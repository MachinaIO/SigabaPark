---
title: Coupling the reachable target rows after the Bonsai complement switch
refs: [definition:WE_CircuitSAT]
tags: [witness-encryption, reduction, simulation]
---

In the displayed simulator of [PR 111 section 2](https://github.com/MachinaIO/SigabaPark/blob/d0cdda51bd1354fe7f0a5cbb9e08e57ac6a8a48b/dag/Notes/pq-we-exposed-root-reachable-lemma.md),
the hidden challenge secret is C1 in -C1 X1 + E_chal. The separate summand
P' S_hat A_i is supplied by the reduction. Changing this summand by a
computable amount is permitted on the uniform-complement side: translation
of its fresh uniform block preserves the law (the amount must be fixed
independently of that block). A factorization C1 H is a sufficient route
for a hidden response offset but is not required for this known summand.
The reachable coordinates V' S_hat A_i, shared state at the next level,
and the prerequisites for using the lemma in *both* programs still matter.

**An exact test for a restricted shared-state hybrid.** Work mod q.
Conditional on fixed sampled transition matrices, suppose the fresh hidden
next-level column a is uniform and enters the rest of the hybrid via known
linear readings J a and the target rows only. For program b in {0,1}
stack all its reachable target matrices into M_b (including both input
bit branches when they share a), with affine constant k_b. Stack J to
include all retained linear data, not just a single prefix reading.
Define F_b=[J;M_b] and c_b=(0,k_b). The clean joint law is uniform on
c_b+im F_b. It is identical for the two programs iff the generated
submodules coincide and c_0-c_1 is in that common image. At composite
q compute the image by adjoining qI to lifted columns and taking an
integer Hermite basis. If the test passes, a simulator can explicitly
couple states: start from a_0, compute its joint reading and sample a_1
uniformly among solutions F_1 a_1=F_0 a_0+c_0-c_1 using Smith form.
Then a_1 is uniform unconditionally, with all the specified readings
matched. For conditionally independent fresh columns, repeat per column.
A retained noisy target can be obtained by adding the same independent
noise after coupling. Any further randomized public output drawn by a
common conditional kernel from these matched readings also couples.
An already-fixed nonlinear descendant or a preimage conditional on a
different secret matrix need not have such a kernel.

**Failure certificate and effect of noise.** For distinct clean affine
images the exact TV is 1-|intersection|/max(|im F_0|,|im F_1|), hence at
least 1/2. More specifically take any finite-group character chi and
write E_b chi = chi(c_b) if chi annihilates im F_b, zero otherwise.
After independent common additive noise N, TV is at least half the
absolute difference of these two expectations times |E chi(N)|.
This follows by taking expectations of the bounded complex character.
It permits testing the particular projected noise before concluding
that a mismatch is hidden. It concerns joint simulator data; the
adversary need not see clean target rows. As a simple joint-only
obstruction, (u,u) and (u,v) have uniform one-coordinate marginals for
independent uniform scalars, but clean joint TV 1-1/q. The character
of the difference distinguishes their joint laws if the noise preserves
that character. Conversely (u,v) and (u,u+v) couple exactly by a shear
when there is no further reading revealing v.

**Boundary for the frontier.** This test identifies an alternative proof
obligation: match the full reachable projection after the complement has
been randomized, jointly with the retained next-level use, without
shifting the challenge columns at all. PR 113's pair (X+U,U) illustrates
why one must stack readings: subtracting them cancels the common U.
No description of all APG-direct descendants by an admissible J and
common conditional sampler is established here. Neither the short-lift
hypothesis nor the non-co-located point-insertion hop follows from a
positive test on a selected subset of rows.
