---
title: "Task summary: Keep one witness address across local NAND checks with correlated restricted function masks"
tags: [research-summary]
refs: [note:goal-e30dec5ceb4bf12756c8bfa37ac656e9185a83c224ed8b452446988fc9d1832b, theorem:AdvancedEncryption.WE.CommonMask.first_failed_shift, theorem:AdvancedEncryption.WE.CommonMask.literal_isolation, theorem:AdvancedEncryption.WE.CommonMask.residue_cover, theorem:AdvancedEncryption.WE.CommonMask.three_address_leak, theorem:AdvancedEncryption.WE.CommonMask.three_address_repair, theorem:AdvancedEncryption.WE.CommonMask.view_coset]
---

# Task summary: Keep one witness address across local NAND checks with correlated restricted function masks

Task `72b7b1a0-74af-4806-a926-9b38a6d6d922` (design / expand), goal `e30dec5ceb4bf12756c8bfa37ac656e9185a83c224ed8b452446988fc9d1832b`, outcome `verified_partial`. Mathematical status comes from the records, not from this note.

Six Lean solutions and two notes were published. For canonical linear masks the local restriction kernels determine exactly when the complete public transcript hides the endpoint bit. A three-constraint instance admits a three-address distinguisher. Adding one cross term restores perfect hiding in the toy instance, verified by complete enumeration. A mod-three violation-cover family also has a compact statistical construction. General false circuits, a secure succinct aggregate and the full registered WE cost remain open.

```sigaba-summary-v1
{
 "schema": "sigaba.summary.v1",
 "task_id": "72b7b1a0-74af-4806-a926-9b38a6d6d922",
 "goal": "e30dec5ceb4bf12756c8bfa37ac656e9185a83c224ed8b452446988fc9d1832b",
 "outcome": "verified_partial",
 "pr": 172
}
```
