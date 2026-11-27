---
title: Computing the other-prefix reading span in the point-insertion hybrid
refs: [definition:WE_CircuitSAT]
tags: [witness-encryption, security-reduction, linear-algebra]
---

Section 3 of [PR 113](https://github.com/MachinaIO/SigabaPark/blob/54fdd46353a518dd353bf145566e0b0b2c410bbc/dag/Notes/pq-we-point-insertion-frontier.md)
asks whether the target reading of a shared random matrix can mask a single
prefix despite reuse. Reader count alone cannot decide this for an individual
prefix: arbitrarily many other rows might occupy a proper subspace. There
is an exact polynomial-time test on the sampled transition matrices,
including simultaneous linear readings of multiple independent random masks.

Work over a finite field. For prefix x of length h let its complete reading
row be r_x = s M_(1,x1) ... M_(h,xh) of width d (use a direct sum for jointly
observed additive blocks, multiplying independent mask coordinates).
Fixed clause literal tests can be implemented by zeroing disallowed block
transitions. Each row then specifies the single mixed observation r_x U
for a common independent uniform column U. For a fixed target p initialize
t=s and B empty. For the next target bit b compute simultaneously

    B' = basis(B M_(i,0), B M_(i,1), t M_(i,1-b))
    t' = t M_(i,b).

Here B stores independent actual rows; basis selects independent input rows
without changing them. Induction: every other prefix either already differed
or first differs now. The first two sets span all descendants of earlier
divergences by linearity. Thus after h levels t=r_p and B spans exactly all
other rows. Tracking prefix pointers yields at most d actual other prefixes
and field coefficients representing t if t is in the span. Otherwise solve
B v=0, t v=1. The shift U -> U+v a preserves every other observation and
translates the target by any field element a. For a matrix U use a separate
translation per output column. This proves exact conditional uniformity
in that case; in the dependent case the selected readings determine the
target exactly. Preexisting revealed linear readings of U can be appended
at the final rank test if U was initially independent of the coefficients.
Time is O(h d^3) field operations with dense matrices, working space O(d^2)
field elements excluding inputs and optional witness pointers.

**Counting isolated prefixes.** For a fixed bank of rows, every target
outside the span of the others is a coloop, and all such rows are linearly
independent. Thus at most d of N eligible prefixes can receive this
single-target statistical mask, regardless of the distribution of the
matrices. For a uniform eligible target independent of that bank the
probability is at most min(1,d/N). The same counting bound applies to
an independently sampled bank by conditioning. Zero rows outside the
eligible set can be included. With multiple independent banks and a
choice among them, sum their widths for an upper bound by union.
A width polynomial in h cannot isolate all exponentially many readers
in a *common* bank by this argument. A bank programmed separately for each
target changes the quantifiers; the bound does not cover it.

**What this checks.** The decision procedure takes matrices as input; a
simulator that knows their sampled values can use it. Giving real adversaries
secret matrices or individual mask readings is not justified. Actual APG'
has noise, correlations and public preimages; a field-span certificate does
not simulate these, and modular reconstruction coefficients may amplify
noise. In particular no computational distinguishing algorithm or proof of
PI follows. This isolates the joint linear test that a modified bank or an
embedding exposing only mixed observations must pass to use this masking
argument.
