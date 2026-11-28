---
title: "Task summary: Issue one affine evaluation key for implicit row addresses and compress the row-side corrections"
tags: [research-summary]
refs: [definition:WE_IndexedFrame, note:goal-e30dec5ceb4bf12756c8bfa37ac656e9185a83c224ed8b452446988fc9d1832b, theorem:AdvancedEncryption.WE.IndexedIssuer.anchored_chart, theorem:AdvancedEncryption.WE.IndexedIssuer.native_coordinate, theorem:AdvancedEncryption.WE.IndexedIssuer.native_free_frame, theorem:AdvancedEncryption.WE.IndexedIssuer.private_subspace_shares]
---

# Task summary: Issue one affine evaluation key for implicit row addresses and compress the row-side corrections

Task `193a6b05-4436-4516-ab2b-96ab8fe10404` (design / expand), goal `e30dec5ceb4bf12756c8bfa37ac656e9185a83c224ed8b452446988fc9d1832b`, outcome `verified_partial`. Mathematical status comes from the records, not from this note.

The independent-issuer construction for the three-input template beta*(x XOR z)*y has a 29-bit key and 210 bits of public issuance at four rows per party, covering all 64 authorized input tuples. Its joint transcript can be sampled from the authorized outputs. The alternative eager representation uses 1472 bits. Four accepted proof solutions support the finite algebra and joint masks. The construction handles this template, not general CircuitSAT, and its bit ledger is not a complete registered machine cost.

```sigaba-summary-v1
{
 "schema": "sigaba.summary.v1",
 "task_id": "193a6b05-4436-4516-ab2b-96ab8fe10404",
 "goal": "e30dec5ceb4bf12756c8bfa37ac656e9185a83c224ed8b452446988fc9d1832b",
 "outcome": "verified_partial",
 "pr": 162
}
```
