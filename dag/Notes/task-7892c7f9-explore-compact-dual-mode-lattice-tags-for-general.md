---
title: "Task summary: Explore compact dual-mode lattice tags for general circuit witnesses"
tags: [research-summary]
refs: [note:goal-e30dec5ceb4bf12756c8bfa37ac656e9185a83c224ed8b452446988fc9d1832b, theorem:AdvancedEncryption.WE.BranchTags.calbo_key_write_floor, theorem:AdvancedEncryption.WE.BranchTags.dense_gate_write_floor, theorem:AdvancedEncryption.WE.BranchTags.joint_wire_values, theorem:AdvancedEncryption.WE.BranchTags.masked_view_count, theorem:AdvancedEncryption.WE.BranchTags.nand_rectangle_quotient, theorem:AdvancedEncryption.WE.BranchTags.rounded_branch_unique]
---

# Task summary: Explore compact dual-mode lattice tags for general circuit witnesses

Task `7892c7f9-f396-4349-b459-efcc36339e83` (design / expand), goal `e30dec5ceb4bf12756c8bfa37ac656e9185a83c224ed8b452446988fc9d1832b`, outcome `verified_partial`. Mathematical status comes from the records, not from this note.

The BranchTags package gives an exact finite mask-fiber count, characterizes row and column offsets by the NAND rectangle invariant, and proves when local wire assignments can be glued across their shared input support. Two numerical lemmas certify conditional lower bounds of 8,455,716,864 writes for the stated dense per-gate index layout and 15,032,385,536 for the stated literal cumulative-lossy key layout. These bounds use explicit parameters and serialization assumptions. The rounded-branch lemma is a modular uniqueness result. A complete construction still needs an efficient assignment-bound public merge, terminal recovery, a full-view security reduction and a strict aggregate cost below 4,294,967,296. The successor task investigates assignment-bound dataset signatures as a possible merge layer.

```sigaba-summary-v1
{
 "schema": "sigaba.summary.v1",
 "task_id": "7892c7f9-f396-4349-b459-efcc36339e83",
 "goal": "e30dec5ceb4bf12756c8bfa37ac656e9185a83c224ed8b452446988fc9d1832b",
 "outcome": "verified_partial",
 "pr": 133
}
```
