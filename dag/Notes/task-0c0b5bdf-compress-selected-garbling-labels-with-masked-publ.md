---
title: "Task summary: Compress selected garbling labels with masked public lookup constraints from lattice CPRFs"
tags: [research-summary]
refs: [note:goal-e30dec5ceb4bf12756c8bfa37ac656e9185a83c224ed8b452446988fc9d1832b, theorem:AdvancedEncryption.WE.MaskedLookup.masked_kernel, theorem:AdvancedEncryption.WE.MaskedLookup.mixed_output_floor, theorem:AdvancedEncryption.WE.MaskedLookup.table_budget, theorem:AdvancedEncryption.WE.MaskedLookup.terminal_law]
---

# Task summary: Compress selected garbling labels with masked public lookup constraints from lattice CPRFs

Task `0c0b5bdf-8f27-40f7-8f94-84dbdd49afe5` (design / deepen), goal `e30dec5ceb4bf12756c8bfa37ac656e9185a83c224ed8b452446988fc9d1832b`, outcome `verified_partial`. Mathematical status comes from the records, not from this note.

For fixed independent garblings, the encryptor can program the active label on a known message input to a public constant, keeping the unused label secret. This removes the message-side input-label array. The proposed masked-seed design groups independent issuance slots under one scoped key-policy ABE setup. Its privacy argument still needs a quantitative post-quantum instantiation of all primitives and a proof covering the enclosing protocol.

The four-cell terminal selector returns each output bit directly. For an opaque serialized output of width z at recursion depth h, the stated layout requires at least 4^(2^h-1) z bits in the last ciphertext. If each prefix and slot entry is at least 64 bits, no partition of the 128 witness bits fits the strict 2^32 target in this layout. The results leave open other output encodings, the registered security game, joint correctness and complete machine clocks.

```sigaba-summary-v1
{
 "schema": "sigaba.summary.v1",
 "task_id": "0c0b5bdf-8f27-40f7-8f94-84dbdd49afe5",
 "goal": "e30dec5ceb4bf12756c8bfa37ac656e9185a83c224ed8b452446988fc9d1832b",
 "outcome": "verified_partial",
 "pr": 145
}
```
