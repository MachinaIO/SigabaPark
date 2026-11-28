---
title: "Task summary: Correlate two prefix-restricted share keys across one parallel NAND layer and an affine wiring map"
tags: [research-summary]
refs: [note:goal-e30dec5ceb4bf12756c8bfa37ac656e9185a83c224ed8b452446988fc9d1832b, theorem:AdvancedEncryption.WE.PrefixTag.AlternatingWires, theorem:AdvancedEncryption.WE.PrefixTag.FixedExpansionCost, theorem:AdvancedEncryption.WE.PrefixTag.JointLookup, theorem:AdvancedEncryption.WE.PrefixTag.OffsetTransport, theorem:AdvancedEncryption.WE.PrefixTag.RowSlacks, theorem:AdvancedEncryption.WE.PrefixTag.SumsetPeriod]
---

# Task summary: Correlate two prefix-restricted share keys across one parallel NAND layer and an affine wiring map

Task `0be0457a-52e2-4ecd-8b4a-939850c2deb7` (design / expand), goal `e30dec5ceb4bf12756c8bfa37ac656e9185a83c224ed8b452446988fc9d1832b`, outcome `verified_partial`. Mathematical status comes from the records, not from this note.

The task gives a synchronized two-role lookup for a 4096-gate alternating NAND family with a constant or a witness bit at its start. The NO image of the wiring side is separated from the local NAND image. Under the stated fixed decision Ring-LWE assumption the two published restricted descriptions on the NO member can be simulated together. The shorter record counts 8706 raw bits for the public header and both keys. The DAG package contains proofs about the slack and cancellation identities, offset transport, joint lookup, expansion size and periods. The general gate-key issuer, a closed quantum cost/gain reduction and a registered machine bound for arbitrary instances are open.

```sigaba-summary-v1
{
 "schema": "sigaba.summary.v1",
 "task_id": "0be0457a-52e2-4ecd-8b4a-939850c2deb7",
 "goal": "e30dec5ceb4bf12756c8bfa37ac656e9185a83c224ed8b452446988fc9d1832b",
 "outcome": "verified_partial",
 "pr": 219
}
```
