---
title: "Task summary: Program terminal word selection into dedicated garbled output labels by bounded sampling"
tags: [research-summary]
refs: [note:goal-e30dec5ceb4bf12756c8bfa37ac656e9185a83c224ed8b452446988fc9d1832b, theorem:AdvancedEncryption.WE.TerminalTokens.parity_three, theorem:AdvancedEncryption.WE.TerminalTokens.pooled_cutoff, theorem:AdvancedEncryption.WE.TerminalTokens.ternary_floor, theorem:AdvancedEncryption.WE.TerminalTokens.two_bit_decode, theorem:AdvancedEncryption.WE.TerminalTokens.vector_law, theorem:AdvancedEncryption.WE.TerminalTokens.word_decode]
---

# Task summary: Program terminal word selection into dedicated garbled output labels by bounded sampling

Task `057a9a2d-21e9-4ab5-988b-6c2b8f72fad8` (design / deepen), goal `e30dec5ceb4bf12756c8bfa37ac656e9185a83c224ed8b452446988fc9d1832b`, outcome `verified_partial`. Mathematical status comes from the records, not from this note.

A dedicated final wire can carry a two-bit token for hidden selection between its normal value and an encryptor-known override. An existing wide wire admits a three-cell header by parity. For a word of L distinct carriers sharing one control, one programmed bit per carrier permits a header of 2L+1 bits. The note includes the costs of the producing gates, label widths, and PRF calls. Its joint-view argument covers a fixed active path under the specified independent-key and domain assumptions.

The three-cell terminal layout retains a conditional 2^32 exclusion. The 2L+1 header alone leaves an arity-five partition with 3,221,217,280 counted bits under the stated 64-bit front estimate. This is only a necessary ledger. Retaining PRF strength can require an extra bit in each producing cell. A complete registered reduction, a costed supply of suitable carriers, and full machine clocks remain open.

```sigaba-summary-v1
{
 "schema": "sigaba.summary.v1",
 "task_id": "057a9a2d-21e9-4ab5-988b-6c2b8f72fad8",
 "goal": "e30dec5ceb4bf12756c8bfa37ac656e9185a83c224ed8b452446988fc9d1832b",
 "outcome": "verified_partial",
 "pr": 146
}
```
