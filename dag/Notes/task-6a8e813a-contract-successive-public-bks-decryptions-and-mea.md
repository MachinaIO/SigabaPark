---
title: "Task summary: Contract successive public BKS decryptions and measure the first genuinely dynamic boundary"
tags: [research-summary]
refs: [note:goal-e30dec5ceb4bf12756c8bfa37ac656e9185a83c224ed8b452446988fc9d1832b, theorem:AdvancedEncryption.WE.FEPacking.diagonal_cover, theorem:AdvancedEncryption.WE.FEPacking.joint_native_floor, theorem:AdvancedEncryption.WE.FEPacking.second_contraction, theorem:AdvancedEncryption.WE.FEPacking.shard_capacity]
---

# Task summary: Contract successive public BKS decryptions and measure the first genuinely dynamic boundary

Task `6a8e813a-30df-4352-84bd-c20cf6406d1b` (design / deepen), goal `e30dec5ceb4bf12756c8bfa37ac656e9185a83c224ed8b452446988fc9d1832b`, outcome `verified_partial`. Mathematical status comes from the records, not from this note.

For the explicit BKS recursion, contracting the first h selection layers leaves a child of arity r-h and 2^(r-h)-1 literal base decryption calls. Coordinatewise aggregation allows a diagonal set of evaluations to cover each coordinate's choices. With two one-bit chunks followed by fourteen nine-bit chunks, the accounting gives 28,676 objects and 16,383 remaining calls.

The cost exclusion applies to the stated literal AMVY layout and its parameter and key-width hypotheses. The counting results leave open a more compact child implementation, a quantum reduction for the full public view, and a complete cost certificate below 2^32.

```sigaba-summary-v1
{
 "schema": "sigaba.summary.v1",
 "task_id": "6a8e813a-30df-4352-84bd-c20cf6406d1b",
 "goal": "e30dec5ceb4bf12756c8bfa37ac656e9185a83c224ed8b452446988fc9d1832b",
 "outcome": "verified_partial",
 "pr": 143
}
```
