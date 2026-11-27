---
title: "Task summary: Eliminate a jointly affine witness block with variable rank in the residual coordinates"
tags: [research-summary]
refs: [definition:ColumnElimination, note:goal-e30dec5ceb4bf12756c8bfa37ac656e9185a83c224ed8b452446988fc9d1832b, theorem:AdvancedEncryption.WE.ColumnElimination.backsolve_length, theorem:AdvancedEncryption.WE.ColumnElimination.backsolve_remainder, theorem:AdvancedEncryption.WE.ColumnElimination.first_one_valid, theorem:AdvancedEncryption.WE.ColumnElimination.image_reach, theorem:AdvancedEncryption.WE.ColumnElimination.pivot_step, theorem:AdvancedEncryption.WE.ColumnElimination.variable_rank]
---

# Task summary: Eliminate a jointly affine witness block with variable rank in the residual coordinates

Task `6b2f0616-9102-4d44-8205-593bd5c46a8b` (design / deepen), goal `e30dec5ceb4bf12756c8bfa37ac656e9185a83c224ed8b452446988fc9d1832b`, outcome `verified_partial`. Mathematical status comes from the records, not from this note.

This task constructs a witness-preserving projection for a selected block of Boolean variables when the checked equations are jointly affine in that block. The coefficients can depend on retained inputs, so the numerical rank can vary between witnesses. A registered 128-input, 4096-NAND example projects to 80 inputs with 238 live NANDs after synthesis. An accepting residual witness can be lifted back to the source. The method does not guarantee an eligible block or enough compression on an arbitrary circuit. The remaining obligations include a general encryption backend, its quantum security reduction, and the full registered cost.

```sigaba-summary-v1
{
 "schema": "sigaba.summary.v1",
 "task_id": "6b2f0616-9102-4d44-8205-593bd5c46a8b",
 "goal": "e30dec5ceb4bf12756c8bfa37ac656e9185a83c224ed8b452446988fc9d1832b",
 "outcome": "verified_partial",
 "pr": 163
}
```
