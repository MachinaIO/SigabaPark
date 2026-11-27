---
title: "Task summary: Compile registered NAND DAGs to ordered two-key ideal queries with shared-wire provenance"
tags: [research-summary]
refs: [definition:OrderedNand, note:goal-e30dec5ceb4bf12756c8bfa37ac656e9185a83c224ed8b452446988fc9d1832b, theorem:AdvancedEncryption.WE.OrderedIdeal.clean_extends, theorem:AdvancedEncryption.WE.OrderedIdeal.full_fold, theorem:AdvancedEncryption.WE.OrderedIdeal.issued_valid, theorem:AdvancedEncryption.WE.OrderedIdeal.log_sound, theorem:AdvancedEncryption.WE.OrderedIdeal.row_exact, theorem:AdvancedEncryption.WE.OrderedIdeal.target_witness]
---

# Task summary: Compile registered NAND DAGs to ordered two-key ideal queries with shared-wire provenance

Task `27461f1d-6347-4a4a-a924-e1286049ac1b` (design / expand), goal `e30dec5ceb4bf12756c8bfa37ac656e9185a83c224ed8b452446988fc9d1832b`, outcome `verified_partial`. Mathematical status comes from the records, not from this note.

Six verified Lean submissions establish the ordered row, ideal-log and target-witness lemmas for the registered NAND evaluation. In a clean derivation reaching the designated accepting label, there exists a satisfying witness. The final commit also contains the compiler definition and replay note. The proof relies on the clean ideal interface; a setup-free real implementation with full-view post-quantum security and a sub-2^32 registered cost remains open.

```sigaba-summary-v1
{
 "schema": "sigaba.summary.v1",
 "task_id": "27461f1d-6347-4a4a-a924-e1286049ac1b",
 "goal": "e30dec5ceb4bf12756c8bfa37ac656e9185a83c224ed8b452446988fc9d1832b",
 "outcome": "verified_partial",
 "pr": 177
}
```
