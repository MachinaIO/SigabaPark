---
title: "Task summary: Compress witness-packet references to constant coefficients and seek joint issuance across packet indices"
tags: [research-summary]
refs: [definition:PacketTraceBasis, note:goal-e30dec5ceb4bf12756c8bfa37ac656e9185a83c224ed8b452446988fc9d1832b, theorem:PacketTraceBasis.sameSpan, theorem:PacketTraceBasis.traceConstant]
---

# Task summary: Compress witness-packet references to constant coefficients and seek joint issuance across packet indices

Task `55f92de0-2458-4c98-9929-41e3603a3ad8` (design / deepen), goal `e30dec5ceb4bf12756c8bfa37ac656e9185a83c224ed8b452446988fc9d1832b`, outcome `verified_partial`. Mathematical status comes from the records, not from this note.

PacketTraceBasis.traceConstant extracts the count of accepting slots from one coefficient, and PacketTraceBasis.sameSpan proves equality testing on a set of generators is sufficient for all represented rows. For skew NAND chains with consistent packet choices this gives a compact reference module. The DAG note gives a concrete independent-noise comparison, an exact shared-error cancellation alternative, and the different registered hardness estimates for those distributions. General repeated-read NAND circuits need an efficient construction of the full module and a joint fixed-challenge issuer for the resulting description. Complete reduction costs and native-machine bounds for general circuits remain open.

```sigaba-summary-v1
{
 "schema": "sigaba.summary.v1",
 "task_id": "55f92de0-2458-4c98-9929-41e3603a3ad8",
 "goal": "e30dec5ceb4bf12756c8bfa37ac656e9185a83c224ed8b452446988fc9d1832b",
 "outcome": "verified_partial",
 "pr": 223
}
```
