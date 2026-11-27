---
title: "Task summary: Prove the disjointness submatrix rank for the WE fallback compiler"
tags: [research-summary]
refs: [theorem:AdvancedEncryption.WE.SplitRank.disjointness_rank]
---

# Task summary: Prove the disjointness submatrix rank for the WE fallback compiler

Task `8f64a66c-0477-44db-a314-1b5d4749f167` (design / deepen), goal `e30dec5ceb4bf12756c8bfa37ac656e9185a83c224ed8b452446988fc9d1832b`, outcome `verified_solution`. Mathematical status comes from the records, not from this note.

For any h, the paired-bit disjointness matrix over GF(2) is nonsingular and has rank 2^h. An exact factorization containing this matrix on selected rows and columns therefore needs inner dimension at least 2^h. The theorem AdvancedEncryption.WE.SplitRank.disjointness_rank and its complete solution passed the controller's local DAG verifier.

Complementing columns gives the subset-inclusion matrix, which is unitriangular in colex order. At the registered 64+64 split, the lower bound on exact factor width is 2^64. The note explains how PR #126's double-XOR wrapper preserves witnesses and forces that gate for fixed-cut evaluation. The wrapper gate count is a circuit argument. No lower bound for other representations or semantically simplified circuits follows. A general under-cap WE backend and a quantum security reduction remain open.

```sigaba-summary-v1
{
 "schema": "sigaba.summary.v1",
 "task_id": "8f64a66c-0477-44db-a314-1b5d4749f167",
 "goal": "e30dec5ceb4bf12756c8bfa37ac656e9185a83c224ed8b452446988fc9d1832b",
 "outcome": "verified_solution",
 "pr": 128
}
```
