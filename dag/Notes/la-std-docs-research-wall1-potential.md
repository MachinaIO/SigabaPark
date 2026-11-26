---
title: "A packing obstruction for nets of prefix projections"
refs: []
tags: [lattice-attack]
---
*Moved from `docs/research/wall1_potential.md` (core v0.1.2).*

# A packing obstruction for nets of prefix projections

Even at a fixed rank, small integer descriptions alone cannot give a polynomial
net in operator norm. In dimension 2m split the coordinate axes into m pairs.
Choose one axis per pair and project onto their span. Each resulting rank-m
projection has a diagonal matrix with entries in {0,1}. Each span is a
primitive coordinate prefix for a permutation basis of the integer lattice.

Two different choices disagree on a unit coordinate vector, so their operator
distance is at least one. More generally, if a common center C approximates
both with error strictly below 1/2, every diagonal entry of C approximates both
corresponding bits with error strictly below 1/2, since
|⟨eᵢ,(P−C)eᵢ⟩| ≤ ‖P−C‖. The Lean theorem
`uniqueDiagonal` proves the resulting uniqueness of the binary diagonal.
Thus any such cover needs at least 2^m centers. This counting deduction is
on paper. It applies even when centers need not be projections. The example
concerns the family of all these prefixes. Reachability under a particular
tour and initialization is an additional restriction. Permutation symmetry
can also make these well-separated projections equivalent for a particular
observable. A useful net would need an observable-specific stability or
symmetry argument, or a smaller reachable family.

## What a potential estimate would give

Let P(t) denote the expected potential after t updates in a finite ensemble.
Suppose the realized potential never increases and drops by at least η>0 on
a designated event Bₜ. Taking expectations on the original sample space gives
η Pr(Bₜ) ≤ P(t)−P(t+1), even when the block choice depends on the input.
Applying `driftBudget` shows that the mean of these event probabilities
over T>0 updates is at most (P(0)−P(T))/(ηT). The Lean theorem formalizes
the telescoping inequality. The event interpretation follows by linearity.

The drift premise would need to connect a *selected* profile defect to actual
progress. The fixed-coordinate result in [wall2b](wall2b.md) controls a dual
minimum for a different sampling rule and supplies no such implication.
Even a time-average bound permits a large last-iterate defect. A terminal
profile claim needs a persistence or contraction argument. Neither a
finite-tour average profile slope nor a concrete block size follows here.
