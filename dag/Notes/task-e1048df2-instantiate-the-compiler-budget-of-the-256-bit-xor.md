---
title: "Task summary: Instantiate the compiler budget of the 256-bit XOR-lock circuit"
tags: [research-summary]
refs: [definition:WE_GKW_Trace, note:goal-e30dec5ceb4bf12756c8bfa37ac656e9185a83c224ed8b452446988fc9d1832b, theorem:AdvancedEncryption.WE.GKW.base_field_floor, theorem:AdvancedEncryption.WE.GKW.component_parameters, theorem:AdvancedEncryption.WE.GKW.essential_blocks, theorem:AdvancedEncryption.WE.GKW.trace_unique]
---

# Task summary: Instantiate the compiler budget of the 256-bit XOR-lock circuit

Task `e1048df2-b4e4-438b-ad57-9490cf52ac55` (design / deepen), goal `e30dec5ceb4bf12756c8bfa37ac656e9185a83c224ed8b452446988fc9d1832b`, outcome `verified_partial`. Mathematical status comes from the records, not from this note.

For the literal general-circuit compiler of Goyal, Koppula and Waters, the number and dimensions of the published starting matrices already preclude the strict clock budget for PR 131's 256-bit XOR-header program. Let L be the common branching-program length. Under the stated finite sampler and parameter inequalities, the base field contains at least 25(12L)^10 fixed-width bits. The literal schedule has L at least 256, giving over 2^120 raw base bits before transition matrices and the LHE fields. This is a lower bound for one compiler and parameter analysis. It has no implication for the size of an arbitrary post-quantum WE. The correlated-header reduction remains unresolved, and a construction under 2^32 would require a different encoding/distribution or a different proven finite parameter regime.

```sigaba-summary-v1
{
 "schema": "sigaba.summary.v1",
 "task_id": "e1048df2-b4e4-438b-ad57-9490cf52ac55",
 "goal": "e30dec5ceb4bf12756c8bfa37ac656e9185a83c224ed8b452446988fc9d1832b",
 "outcome": "verified_partial",
 "pr": 136
}
```
