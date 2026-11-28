---
title: "Task summary: Compile shared projected witness predicates without expanding every cofactor"
tags: [research-summary]
refs: [definition:LinearObservationJoin, definition:LinearProjectNative, note:goal-e30dec5ceb4bf12756c8bfa37ac656e9185a83c224ed8b452446988fc9d1832b, theorem:AdvancedEncryption.WE.LinearProjection.costs, theorem:AdvancedEncryption.WE.LinearProjection.forcedFrequency, theorem:AdvancedEncryption.WE.LinearProjection.fourGroups, theorem:AdvancedEncryption.WE.LinearProjection.glue, theorem:AdvancedEncryption.WE.LinearProjection.oneReference, theorem:AdvancedEncryption.WE.LinearProjection.polarity, theorem:AdvancedEncryption.WE.LinearProjection.rectangle, theorem:AdvancedEncryption.WE.LinearProjection.splitJoin]
---

# Task summary: Compile shared projected witness predicates without expanding every cofactor

Task `caa0f704-9438-4da5-91a8-422c7b389775` (design / deepen), goal `e30dec5ceb4bf12756c8bfa37ac656e9185a83c224ed8b452446988fc9d1832b`, outcome `verified_partial`. Mathematical status comes from the records, not from this note.

LinearProjection.glue and splitJoin characterize when two child witnesses extend to a common NAND witness in an affine fiber. The forcedFrequency and rectangle results quantify conditional tests. LinearProjection.fourGroups and costs establish a concrete common-parity family with 120 eliminated bits and all 256-bit truth tables on the eight retained inputs. The native encoder and decoder have joint registered cost 234208399 for this restricted family, and table-driven replays exercised all table and payload pairs. An all-input machine bisimulation, an efficient uniform projection for arbitrary NAND circuits, and a fixed-assumption post-quantum reduction with complete costs remain open. Improving the general compiler requires controlling the total number of distinct conditioned states, including their ancestor constraints.

```sigaba-summary-v1
{
 "schema": "sigaba.summary.v1",
 "task_id": "caa0f704-9438-4da5-91a8-422c7b389775",
 "goal": "e30dec5ceb4bf12756c8bfa37ac656e9185a83c224ed8b452446988fc9d1832b",
 "outcome": "verified_partial",
 "pr": 222
}
```
