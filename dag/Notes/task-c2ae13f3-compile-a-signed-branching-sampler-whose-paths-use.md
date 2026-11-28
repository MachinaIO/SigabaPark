---
title: "Task summary: Compile a signed branching sampler whose paths use legal NAND rows"
tags: [research-summary]
refs: [note:goal-e30dec5ceb4bf12756c8bfa37ac656e9185a83c224ed8b452446988fc9d1832b, theorem:AdvancedEncryption.WE.LegalBranch.BoundaryMass, theorem:AdvancedEncryption.WE.LegalBranch.FiberCoin, theorem:AdvancedEncryption.WE.LegalBranch.FoldPayload, theorem:AdvancedEncryption.WE.LegalBranch.FullViewCount, theorem:AdvancedEncryption.WE.LegalBranch.LeafLine, theorem:AdvancedEncryption.WE.LegalBranch.LeafTransfer, theorem:AdvancedEncryption.WE.LegalBranch.SelectSign]
---

# Task summary: Compile a signed branching sampler whose paths use legal NAND rows

Task `c2ae13f3-048b-49b7-abe0-c8d4524c7592` (design / expand), goal `e30dec5ceb4bf12756c8bfa37ac656e9185a83c224ed8b452446988fc9d1832b`, outcome `verified_partial`. Mathematical status comes from the records, not from this note.

The legal-branch sign issuer has identical whole-view laws on false circuits. Its message distance on true circuits is characterized by witness-trace survival for the specified sampler. Seven Lean component proofs passed. Reverse traversal recovers the witness on the full-sized comparator fixture; neither that fixture nor the three-gate exhaustive replay gives a uniform survival bound on arbitrary circuits. A general sampler with sufficient correctness and a registered total clock is still open.

```sigaba-summary-v1
{
 "schema": "sigaba.summary.v1",
 "task_id": "c2ae13f3-048b-49b7-abe0-c8d4524c7592",
 "goal": "e30dec5ceb4bf12756c8bfa37ac656e9185a83c224ed8b452446988fc9d1832b",
 "outcome": "verified_partial",
 "pr": 250
}
```
