---
title: "Task summary: Determine the strict 32-bit feasibility frontier for sealed row issuance"
tags: [research-summary]
refs: [note:goal-e30dec5ceb4bf12756c8bfa37ac656e9185a83c224ed8b452446988fc9d1832b, theorem:AdvancedEncryption.WE.SealedRow.compact_input_frontier, theorem:AdvancedEncryption.WE.SealedRow.decoder_write_budget, theorem:AdvancedEncryption.WE.SealedRow.encoded_frontier, theorem:AdvancedEncryption.WE.SealedRow.fused_conversion_frontier, theorem:AdvancedEncryption.WE.SealedRow.output_cost, theorem:AdvancedEncryption.WE.SealedRow.pair_seed_bijection, theorem:AdvancedEncryption.WE.SealedRow.selected_phase_parity]
---

# Task summary: Determine the strict 32-bit feasibility frontier for sealed row issuance

Task `9013c93d-6d81-4ad1-bec4-67b2051bcc5c` (design / deepen), goal `e30dec5ceb4bf12756c8bfa37ac656e9185a83c224ed8b452446988fc9d1832b`, outcome `verified_partial`. Mathematical status comes from the records, not from this note.

The sealed-row-conversion-frontier note and accompanying arithmetic proofs price the concrete dense conversion of PR 129 for every witness split. Its direct framed output alone exceeds the strict aggregate budget. Public addition of selected scalar ciphertexts permits one protected parity decryption per tape row, with correctness for the stated bounded errors. This retains the original dense seed law while narrowing the possible widths for a literal sampler. The filters bound serialized fields and necessary write slots. A complete tape implementation, concrete sampling and compiler parameters, registry reduction for the correlated setup, and an upper bound for the full WE remain open.

```sigaba-summary-v1
{
 "schema": "sigaba.summary.v1",
 "task_id": "9013c93d-6d81-4ad1-bec4-67b2051bcc5c",
 "goal": "e30dec5ceb4bf12756c8bfa37ac656e9185a83c224ed8b452446988fc9d1832b",
 "outcome": "verified_partial",
 "pr": 130
}
```
