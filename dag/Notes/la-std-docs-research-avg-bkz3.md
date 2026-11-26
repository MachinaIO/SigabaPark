---
title: "Fixed-prefix moments under adaptive selection"
refs: []
tags: [lattice-attack]
---
*Moved from `docs/research/avg_bkz3.md` (core v0.1.2).*

# Fixed-prefix moments under adaptive selection

The number of prefixes visited on one run cannot serve as the size of the
family in a union bound. This issue already occurs for one selection, with
bounded observations and exact knowledge of every fixed-index moment.

Let the input X be uniform on N labels, and set C_i(X) = 1[X=i].
For every fixed i and every positive integer k, E[C_i^k] = 1/N.
Selecting I=X gives E[C_I^k] = 1. The union over all N possible choices is
sharp, although each run uses just one label. For N exponential in the input
bit length even a single selection can incur exponential amplification.
The Lean theorem `SigabaNeo.AvgBKZ.diagonalSelectionCounts` counts the
two event sizes before division by N. This is a counterexample to an inference
from marginal moments alone. It does not identify these indicators with
actual short-vector counts.

**Randomized selection.** Give label X weight N−1 and each other label
weight one, for N at least two. Sampling proportionally to these positive
weights hits X with probability (N−1)/(2N−2) = 1/2 for every input.
By symmetry the selected label itself is uniform. Thus even a uniform
output marginal and full support do not control selection bias. The
normalization identity is `SigabaNeo.AvgBKZ.diagonalWeightHalf`, with
N=n+2. This finite example does not assert that lattice discrete Gaussians
have these weights.

**Independent choices.** For an input-independent I, conditioning on I=i
preserves the input law, and the selected failure probability is the weighted
average of the fixed-index failure probabilities. Independent signed
permutations of the integer coordinate axes preserve lengths and take
coordinate flags to coordinate flags, so they inherit the grid event in
[the coordinate-flag audit](avg_bkz_audit.md). In fact every orthogonal
integer matrix is a signed permutation: each column has integer entries
whose squares sum to one, and orthogonality forces distinct occupied rows.
General independent unimodular changes lack this isometry property.

A tour-specific conditional estimate, or a simultaneous estimate over a
fixed family containing every attainable prefix, could escape the diagonal
example. Neither the cardinality calculation nor independent coordinate
randomization establishes a post-reduction height at d−β, the joint projected
planted norm, or a cost improvement.
