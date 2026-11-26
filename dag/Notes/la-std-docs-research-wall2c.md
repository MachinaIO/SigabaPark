---
title: "Adaptive blocks and the price of a finite description"
refs: []
tags: [lattice-attack]
---
*Moved from `docs/research/wall2c.md` (core v0.1.2).*

# Adaptive blocks and the price of a finite description

A union bound works for a dictionary of fixed **procedures** on the input
distribution. Each procedure needs a short-dual tail in the Euclidean metric
of its own projected block. Bounded description length alone supplies only
the number of terms. In particular, the fixed-coordinate estimate of
[wall2b.md](wall2b.md) fails for some fixed, succinct oblique flags.

## A one-description geometric obstruction

Use the rank-zero parity check on three columns, giving the primal grid
ℤ³ (also the conditional rank-zero ensemble). Complete the primitive
prefix vector (M,1,0) by (1,0,0) and (0,0,1) to a unimodular basis.
Project out the prefix and retain the two remaining columns. Their projections
are orthogonal and have lengths 1/L and 1, where L = √(1+M²).
The projected determinant is 1/L. After determinant normalization the
dual has orthogonal spacings √L and 1/√L. At r = 1/6 the short-dual
event therefore has conditional probability one for L ≥ 36. The proposed
fixed-coordinate bound (3r)² would give only 1/4. A fixed flag can thus
fail before there is any adaptive selection. Written in the oblique basis,
the residue coordinates still describe the grid, but their Euclidean metric
has changed.

At width R and budget 0 < ε < 2, put C = √(log(2/ε)/π).
For this flag the inherited opposite dual witnesses force every successful
index to obey p ≥ L (C/R)² by [wall2.md](wall2.md). The flag takes
O(log M) bits and this necessary index grows linearly in M for fixed R, ε.
An exact BKZ shortest-prefix step on the grid would choose a unit vector.
This example obstructs extending the marginal estimate to a dictionary by
description size alone. It makes no claim about how often BKZ visits this flag.

## Conditional calculation and tightness

Suppose N fixed descriptions define blocks on the same probability space and
each satisfies Pr[λ₁(Dᵢ) ≤ r] ≤ (3r)^d at the radius in question.
Then r = (δ/N)^(1/d)/3 gives simultaneous failure probability at most δ
for 0 < δ < 1. This covers any number of visits or revisits within the
dictionary. For variable-length binary descriptions of at most b bits one
may take N ≤ 2^(b+1)−1. On success the index computed as
max(1, ceil((C/(R λ₁(D_selected)))^d)) is at most
max(1, ceil((3C/R)^d N/δ)). This rounds up a **necessary** pair threshold.
Computing or certifying the dual minimum has its own cost.

The factor N is sharp from marginal data alone. On N equiprobable inputs
let description i fail exactly at i, and select the input's own description.
Each marginal is 1/N and the selected event has probability one. In
particular, enumerating possible output lattices and assigning each its
probability under an independent coordinate-code draw changes the sample law.
An approximate metric net would additionally require distortion control and
a corresponding radius margin.

The finite counting inequality and its diagonal equality example are
machine-checked as `Wall2.adaptiveFailures` and `Wall2.diagonalSelection`.
The flag computation and the conditional radius and index formulas above
are paper arguments. To bound the sieve cost for actual BKZ requires tails
for the reachable flags or their joint selection law, and control of the
new dual vectors introduced by sublattice selection. Even a smoothing bound
would still require the sieve's shell, sampling, and solution-transfer
hypotheses. No end-to-end cost follows from this union bound.
