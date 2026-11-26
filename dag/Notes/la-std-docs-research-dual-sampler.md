---
title: "A finite short-direction sampler for the fresh dual test"
refs: []
tags: [lattice-attack]
---
*Moved from `docs/research/dual_sampler.md` (core v0.1.2).*

# A finite short-direction sampler for the fresh dual test

Fix an arbitrary public matrix with m rows and n columns over Z/q, q > 1.
Compute the syndrome xA of each of the S = 2^m binary row vectors x.
Form the list K of ordered pairs (x,y) of distinct rows of this table with equal
syndromes. Draw an index uniformly with replacement from K and output x−y
modulo q. Each draw uses the same table for the fixed public A.

When S > q^n, pigeonhole gives K nonempty for every A, including draws from
the uniform matrix ensemble. Equal syndromes give (x−y)A = 0. Distinct
binary vectors differ by ±1 somewhere, so the output survives reduction even
for composite q. Its integer lift has entries in {−1,0,1} and norm at most
√m. The exact mass of w is its ordered-pair multiplicity divided by |K|.
Repeated differences can therefore have different masses.

In the product experiment of binaryDualTest, each of N draws uses a fresh
independent right-hand side for the same matrix and secret. For errors with
integer lifts bounded coordinatewise by B, set ε = 1 − (2πmB/q)²/2.
For ε > 0, δ > 0, N > 0 and N ≥ 8 log(1/δ)/ε², the acceptance probability
on LWE exceeds the uniform acceptance probability by at least 1−2δ.
For a positive gap use δ < 1/2. The matrix guarantee needs no rank estimate.

## Cost and scope

In the dense arithmetic model, fill the syndrome table once, then compute
the N character arguments. The Lean sum identity counts exactly S n m + N m
ring multiplications for these loops. A direct double scan of the table takes
at most S² pair visits and n coordinate comparisons per syndrome comparison.
Store pair indices using O(|K|) index words in addition to the syndrome table
of S n residues. A uniform array index can be drawn by rejection on
ceil(log₂ |K|) random bits, with fewer than two trials in expectation
(and zero random bits for a singleton). Materializing a difference takes O(m)
coordinate operations per draw. The comparison, memory and random-bit bounds
are paper analyses. Lean specifies the finite law and counts the dense loop
indices. It does not certify a compiled table implementation, cosine evaluation
precision or a bit-operation runtime.

The identity matrix has trivial modular kernel (identity_obstruction), so an
unconditional claim for all dimensions fails. The sufficient dimension
inequality here can require many more samples than m > n. For smaller m it
remains possible that a particular matrix has a collision. The bias estimate
also requires mB < q/(√2π), where the denominator means π times √2.
A discrete Gaussian on the entire dual lattice puts positive probability on
zero and has unbounded support in positive dimension. A GPV route would
therefore need conditioning and quantitative acceptance analysis to meet the
same support contract. Practical BKZ costs and single-right-hand-side
experiments remain outside this result.
