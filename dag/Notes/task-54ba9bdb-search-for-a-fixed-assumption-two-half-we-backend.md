---
title: "Task summary: Search for a fixed-assumption two-half WE backend with succinct encrypted tables"
tags: [research-summary]
refs: [theorem:AdvancedEncryption.WE.Table.coordinate_atoms]
---

# Task summary: Search for a fixed-assumption two-half WE backend with succinct encrypted tables

Task `54ba9bdb-e25b-4bdb-b00f-626e688d9846` (design / expand), goal `e30dec5ceb4bf12756c8bfa37ac656e9185a83c224ed8b452446988fc9d1832b`, outcome `candidate`. Mathematical status comes from the records, not from this note.

The candidate replaces the left half-witness key table by a locked program issuing a residual BGG policy key for the supplied address and keeps an explicit table of right-hand encryptions. The research note specifies the two concrete setup laws and the auxiliary public encryptions that a simulator must reproduce. A false instance has no accepting row in any column. Given the full setup switch, real-side noise comparison and appropriate fixed LWE hardness, a hybrid changing one designated lock bit per column bounds the full-view distinguishing gap. With 12 right-address bits and a 256-bit lock there are 2^12 hybrid positions and the right-hand table still has 2^20 one-bit components. Neither the setup switch nor the registered cost cap has been proved.

The independent algebraic result AdvancedEncryption.WE.Table.coordinate_atoms establishes that closure of a linear function space under each positive coordinate mask yields every supported address indicator. Thus a full-support exact linear packing that keeps the same space under all masks needs a slot per address. The idealized small-circuit checks exercise the framing logic only. The sealed construction's correctness error, implementation clocks and quantum security reduction require further work.

```sigaba-summary-v1
{
 "schema": "sigaba.summary.v1",
 "task_id": "54ba9bdb-e25b-4bdb-b00f-626e688d9846",
 "goal": "e30dec5ceb4bf12756c8bfa37ac656e9185a83c224ed8b452446988fc9d1832b",
 "outcome": "candidate",
 "pr": 129
}
```
