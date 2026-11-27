---
title: "Task summary: Specialize garbling by input ownership while hiding message values and preserving row shape"
tags: [research-summary]
refs: [definition:OwnedGarbling, note:goal-e30dec5ceb4bf12756c8bfa37ac656e9185a83c224ed8b452446988fc9d1832b, theorem:AdvancedEncryption.WE.OwnedGarbling.affine_decode, theorem:AdvancedEncryption.WE.OwnedGarbling.affine_view, theorem:AdvancedEncryption.WE.OwnedGarbling.joint_affine_setup, theorem:AdvancedEncryption.WE.OwnedGarbling.local_value, theorem:AdvancedEncryption.WE.OwnedGarbling.one_cell_complement, theorem:AdvancedEncryption.WE.OwnedGarbling.selector_word, theorem:AdvancedEncryption.WE.OwnedGarbling.whole_graph]
---

# Task summary: Specialize garbling by input ownership while hiding message values and preserving row shape

Task `e3f1d19a-a4c6-405e-a5f7-3b0a5201da95` (design / deepen), goal `e30dec5ceb4bf12756c8bfa37ac656e9185a83c224ed8b452446988fc9d1832b`, outcome `verified_partial`. Mathematical status comes from the records, not from this note.

The finite affine key-issuance template admits exact joint simulation of its public fixed-batch records given the authorized outputs. For one key slot, four rows and 2049 returned key bits, one instance uses 34835 private setup bits and 43031 public bits. Seven submitted proofs cover the wire specialization, word selector and affine construction.

The full BKS aggregator also contains nonlinear operations with private inputs. A private construction for that step, recursive resource accounting, an end-to-end post-quantum reduction, and a total registered cost below 2^32 remain open.

```sigaba-summary-v1
{
 "schema": "sigaba.summary.v1",
 "task_id": "e3f1d19a-a4c6-405e-a5f7-3b0a5201da95",
 "goal": "e30dec5ceb4bf12756c8bfa37ac656e9185a83c224ed8b452446988fc9d1832b",
 "outcome": "verified_partial",
 "pr": 153
}
```
