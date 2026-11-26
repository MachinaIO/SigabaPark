---
title: "Exact insertion and the posterior of an overlapping block"
refs: []
tags: [lattice-attack]
---
*Moved from `docs/research/wall1_rejection.md` (core v0.1.2).*

# Exact insertion and the posterior of an overlapping block

Consider an iid uniform check matrix over a prime field and its integer
modular kernel. Initialize with a deterministic coordinate-adapted Hermite
basis. Fix a block size at least two and visit consecutive blocks once from
left to right, truncating at the right edge. The following exact variant
makes both the expected profile and the bias of the next block explicit.

For a current projected block basis with Gram matrix G, take the shell of
shortest nonzero vectors, identifying signs by first nonzero coefficient
positive. Compute the minimum by enumeration up to squared radius G₁₁.
This enumeration is finite and effective: a vector with zᵀGz ≤ R² satisfies
|zⱼ|² ≤ R²(G⁻¹)ⱼⱼ by Cauchy–Schwarz. Use the resulting rounded-out integer
box for proposals. Draw independent uniform box points until one belongs to
the shell with canonical sign. If its size is a and the box size is b, each
shell point is returned with probability ∑ₖ≥₀ (1−a/b)ᵏ/b = 1/a.
Expected trials are b/a. Exact rational squared norms suffice, including for
orthogonal projections via Gram matrices. A shortest coefficient tuple is
primitive since division by a common factor would shorten it. Complete it
to a unimodular block transform, deterministically by extended gcd with
fixed tie conventions, and use that transform on the unprojected block.
This specifies a randomized exact block reduction, including equal-length
ties. It may be expensive even for a single insertion.

## A conditional obstruction with the Euclidean metric fixed

Take one binary check row (u,v) and a full two-dimensional first block.
Condition on the selected shortest line being the first coordinate axis E.
When u is nonzero that axis cannot be a shortest line: if v=0 the second
unit vector wins, and if v=1 a diagonal of length √2 beats (2,0).
For row (0,0) the two unit axes tie, so the likelihood of E is 1/2.
For row (0,1) only the first unit axis wins. Hence the posterior odds
of (0,0) to (0,1) are 1:2. The suffix after orthogonal projection is
respectively ℤ or 2ℤ. Its conditional probability of spacing one is 1/3.
The Euclidean quotient metric is identical in both cases.

A fresh uniform column in any quotient of the original one-dimensional
binary syndrome space gives spacing one with probability either 1/2 or 1.
Every mixture thus gives at least 1/2. Even allowing arbitrary proportions
of those quotient dimensions cannot recover the posterior. This isolates
selection bias independently of the change of metric in the plane example.
Unconditionally, row (1,1) also gives spacing √2, with probability 1/4,
by area divided by the length of either shortest diagonal. Thus even the
unconditional Euclidean spacing law escapes the fixed-grid family.

## Exact replacement and one-tour expectation

Retain the entire matrix and current basis as the state. For any terminal
profile coordinate f (e.g. squared Gram–Schmidt length), set V_end=f.
At step i with shell C(B), set

    V_i(A,B) = (1 / |C(B)|) ∑_{z ∈ C(B)} V_{i+1}(A, update_i(B,z)).

Conditioning on the first accepted proposal proves the recurrence by backward
induction. Equivalently if g is the sum of continuation values, the retry
equation is x=g/b+(1−a/b)x and has unique solution g/a. The requested initial
expectation is the sum of V_start over all matrices divided by q^(nd).
Taking f to be an indicator instead computes the full projected-block law.
For conditioning on an observed prefix, restrict the finite path sum to that
event and divide by its total mass when positive. Every path weight before
conditioning is q^(−nd) times the product of its inverse shell counts.
This is an exact computable finite mixture of projected lattices with their
actual metrics. It offers no dimension-efficient profile estimate.
For the binary example one can evaluate the full tour directly: the first
squared length averages (1+1+1+2)/4=5/4 and the second averages
(1+4+4+2)/4=11/4, by the area formula (the last singleton cannot change it).

The sieve can average over a frozen good bank because the target distribution
is identical for every such bank. Here the shell itself depends on the basis.
The posterior calculation shows why exact conditional sampling is insufficient
for the analogous fresh-column induction. This disproves that induction for
the specified insertion rule, without excluding other specially designed
rules. Efficient control of adaptive profiles and planted vectors remains open.

The companion Lean file checks the scalar retry identity, binary likelihood
normalization, and mixture contradiction. Enumeration, the lattice realization
of the likelihood table, and the finite-tour recursion are proved above on paper.
