---
title: "Task summary: Eliminate both terminal header rows by jointly programming carrier colors and masks"
tags: [research-summary]
refs: [note:goal-e30dec5ceb4bf12756c8bfa37ac656e9185a83c224ed8b452446988fc9d1832b, theorem:AdvancedEncryption.WE.TerminalZero.word_coupling]
---

# Task summary: Eliminate both terminal header rows by jointly programming carrier colors and masks

Task `cc30ca28-cada-4bfd-9530-1cd89b74e298` (design / deepen), goal `e30dec5ceb4bf12756c8bfa37ac656e9185a83c224ed8b452446988fc9d1832b`, outcome `verified_partial`. Mathematical status comes from the records, not from this note.

The terminal selector uses the two control pads to program the physical orientation of each independently programmable normal wire. One additional bit in its label determines the selected result together with the active pad and colors. The dedicated selection header has length zero. For any finite word, replacing the inactive pad by a uniform word gives an explicit bijection onto uniform active colors. The remaining exposed label bits are then determined by the active pad, colors and allowed output.

This identity is for a fixed evaluation path. Repeated openings, fixed public input labels, correlations with ordinary gate keys, and the production of new carriers require separate analysis. A dedicated unary copy costs four bits in this encoding, and an extra bit per cell of an existing four-row producer costs four bits as well. The fraction of returned bits requiring new producers, the full quantum reduction and the total registered machine cost remain open.

```sigaba-summary-v1
{
 "schema": "sigaba.summary.v1",
 "task_id": "cc30ca28-cada-4bfd-9530-1cd89b74e298",
 "goal": "e30dec5ceb4bf12756c8bfa37ac656e9185a83c224ed8b452446988fc9d1832b",
 "outcome": "verified_partial",
 "pr": 150
}
```
