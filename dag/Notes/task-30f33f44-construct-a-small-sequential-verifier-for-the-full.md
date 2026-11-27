---
title: "Task summary: Construct a small sequential verifier for the full unary NAND relation"
tags: [research-summary]
refs: [definition:WE_UnaryTraceBlocks, definition:WE_UnaryTraceWalk, note:goal-e30dec5ceb4bf12756c8bfa37ac656e9185a83c224ed8b452446988fc9d1832b, theorem:AdvancedEncryption.WE.UnaryTraceWalk.commit_block, theorem:AdvancedEncryption.WE.UnaryTraceWalk.lookup_block, theorem:AdvancedEncryption.WE.UnaryTraceWalk.machine_budget, theorem:AdvancedEncryption.WE.UnaryTraceWalk.run_spec]
---

# Task summary: Construct a small sequential verifier for the full unary NAND relation

Task `30f33f44-27ac-4286-aaba-8face2bb15f7` (design / expand), goal `e30dec5ceb4bf12756c8bfa37ac656e9185a83c224ed8b452446988fc9d1832b`, outcome `verified_partial`. Mathematical status comes from the records, not from this note.

This task supplies a two-work-tape component for checking a 4096-gate NAND trace. On a typed word containing the 128 input bits, 4096 claimed gate values, and the gate stream, the machine checks each NAND against previously computed values with the registered default for forward references. It returns true exactly when the supplied trace is the evaluation trace and its final bit is true. The exact-file gate returned ACCEPTED for AdvancedEncryption.WE.UnaryTraceWalk.lookup_block, commit_block and machine_budget. The composition run_spec returned SKETCH_ACCEPTED. Its two named dependencies are lookup_block and commit_block, both supplied in this PR. Final DAG closure is pending the records for these nodes. The declared clock is 173,064,452 and the canonical description uses 5,728,050 bits, for a component cost of 178,792,502. The WE decryptor would still have to produce or extract this trace and adapt the input format. Encryption, false-statement security, and the full aggregate bound remain open.

```sigaba-summary-v1
{
 "schema": "sigaba.summary.v1",
 "task_id": "30f33f44-27ac-4286-aaba-8face2bb15f7",
 "goal": "e30dec5ceb4bf12756c8bfa37ac656e9185a83c224ed8b452446988fc9d1832b",
 "outcome": "verified_partial",
 "pr": 132
}
```
