---
title: "Task summary: Eliminate mandatory affine witness constraints directly from the raw NAND network"
tags: [research-summary]
refs: [definition:AffineFiberScan, note:goal-e30dec5ceb4bf12756c8bfa37ac656e9185a83c224ed8b452446988fc9d1832b, theorem:AdvancedEncryption.WE.AffineFiberScan.hull_transfer, theorem:AdvancedEncryption.WE.AffineFiberScan.pivot_patch, theorem:AdvancedEncryption.WE.AffineFiberScan.project_lift, theorem:AdvancedEncryption.WE.AffineFiberScan.scan_sound]
---

# Task summary: Eliminate mandatory affine witness constraints directly from the raw NAND network

Task `38d7d4ef-f6ef-4dfd-8dca-184bc837bbeb` (design / expand), goal `e30dec5ceb4bf12756c8bfa37ac656e9185a83c224ed8b452446988fc9d1832b`, outcome `verified_partial`. Mathematical status comes from the records, not from this note.

On the registered mixed 128-input, 4096-NAND fixture, the compiler derived 20 mandatory affine constraints and compressed the remaining predicate to four bits and ten NAND gates. All 16 compressed witnesses lifted correctly; six were accepted. Four verified proof solutions cover the affine-fiber transfer and residual semantics. A circuit with no useful affine constraints retains all 128 inputs. The full registered clock, security reduction and general capped WE remain open.

```sigaba-summary-v1
{
 "schema": "sigaba.summary.v1",
 "task_id": "38d7d4ef-f6ef-4dfd-8dca-184bc837bbeb",
 "goal": "e30dec5ceb4bf12756c8bfa37ac656e9185a83c224ed8b452446988fc9d1832b",
 "outcome": "verified_partial",
 "pr": 157
}
```
