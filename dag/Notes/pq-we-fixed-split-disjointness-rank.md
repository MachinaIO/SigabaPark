---
title: When paired-bit disjointness forces the fixed-split compiler to overflow
refs: [definition:WE_CircuitSAT_Capped, theorem:AdvancedEncryption.WE.SplitRank.disjointness_rank]
tags: [witness-encryption, circuit-sat, linear-algebra]
---

Identify each half-assignment with its set of one bits. The gate
`D = AND_i NAND(x_i, y_i)` outputs one exactly when those sets are disjoint.
Complementing the column support gives the subset-inclusion matrix. In colex
order, a subset precedes every proper superset, so the matrix is upper
triangular with diagonal ones. The Lean theorem proves invertibility over
GF(2), rank exactly 2^h, and the same lower bound on the inner dimension of
any exact factorization whose product contains this table on selected rows
and columns. This includes a gate with extra inputs fixed to obtain the
disjointness restriction.

For the 64/64 split in the registered 128-input problem, a gatewise exact
factorization with cutoff r < 2^64 must overflow by the time it represents
D. To force this event while preserving every witness of a circuit C, use
(C XOR D) XOR D as the output. At h = 64, the 64 pairwise NANDs, 63 binary
ANDs at two NANDs each, and two XORs at four NANDs each add 198 gates.
Thus the wrapper leaves 3898 of the 4096 gate positions for the original
computation, subject to the padding and wire remapping described in
[PR 126](https://github.com/MachinaIO/SigabaPark/pull/126).

If overflow alone dispatches the original wrapped instance to a WE backend,
that backend must preserve correctness for each original witness and
false-statement security for wrapped unsatisfiable circuits across this
whole embeddable family. Overflow gives no promise about satisfiability or
the structure of C. A compiler that simplifies the cancelling XORs before
gatewise evaluation, changes the cut, or uses a different representation
requires a separate analysis. The Lean result covers the matrix and factor
width. The wrapper and gate count above are circuit-level arguments. The
registered machine-cost cap and the security of a general backend remain open.
