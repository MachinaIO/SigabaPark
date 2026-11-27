---
title: "Task summary: Instantiate correlated XOR garbling from modulo-two registry LWE for the projected evaluator"
tags: [research-summary]
refs: [note:goal-e30dec5ceb4bf12756c8bfa37ac656e9185a83c224ed8b452446988fc9d1832b, theorem:AdvancedEncryption.WE.LPNGarble.affine_oracle_row, theorem:AdvancedEncryption.WE.LPNGarble.concatenated_channel_budget, theorem:AdvancedEncryption.WE.LPNGarble.rm_gate_tail_budget]
---

# Task summary: Instantiate correlated XOR garbling from modulo-two registry LWE for the projected evaluator

Task `2573d08b-0f8c-4e9d-aec3-150535544046` (design / expand), goal `e30dec5ceb4bf12756c8bfa37ac656e9185a83c224ed8b452446988fc9d1832b`, outcome `verified_partial`. Mathematical status comes from the records, not from this note.

The DAG contains three machine-checked lemmas covering the affine row, the Reed–Muller tail budget, and the concatenated channel budget. The literal two-gate encoding costs 59,885,568 bits and scaling it to 4,096 gates costs 122,645,643,264 bits. This accounting is for a single evaluation. Full witness encryption, its security reduction, and the required end-to-end cost remain open.

```sigaba-summary-v1
{
 "schema": "sigaba.summary.v1",
 "task_id": "2573d08b-0f8c-4e9d-aec3-150535544046",
 "goal": "e30dec5ceb4bf12756c8bfa37ac656e9185a83c224ed8b452446988fc9d1832b",
 "outcome": "verified_partial",
 "pr": 154
}
```
