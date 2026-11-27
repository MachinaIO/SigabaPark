---
title: "Task summary: Independently assess the fixed rounded related-key pad assumption and its reduction interface"
tags: [research-summary]
refs: [note:goal-e30dec5ceb4bf12756c8bfa37ac656e9185a83c224ed8b452446988fc9d1832b, theorem:AdvancedEncryption.WE.RoundedAudit.adaptive_branch_mass, theorem:AdvancedEncryption.WE.RoundedAudit.dither_pair_bijective, theorem:AdvancedEncryption.WE.RoundedAudit.strict_literal_entropy_budget]
---

# Task summary: Independently assess the fixed rounded related-key pad assumption and its reduction interface

Task `1d2e8f91-4eb2-4437-99cb-c4b5f2018c2c` (cryptanalysis / deepen), goal `e30dec5ceb4bf12756c8bfa37ac656e9185a83c224ed8b452446988fc9d1832b`, outcome `verified_partial`. Mathematical status comes from the records, not from this note.

The frozen rounded related-key projection experiment admits a statistical adaptive classical-query bound for a bounded literal transcript, even with pre-header root leakage of the stated length. Three component Lean proofs were accepted. At lambda 128 the fixed literal bit budget allows 18,053 answers; this is not a full garbled-table width or an expanding-seed security proof. The separate analysis of the static router supports a one-challenge hybrid for its precisely specified auxiliary view. The concrete numerical quantum strength, joint two-block claim, and general witness-dependent supplier remain open.

```sigaba-summary-v1
{
 "schema": "sigaba.summary.v1",
 "task_id": "1d2e8f91-4eb2-4437-99cb-c4b5f2018c2c",
 "goal": "e30dec5ceb4bf12756c8bfa37ac656e9185a83c224ed8b452446988fc9d1832b",
 "outcome": "verified_partial",
 "pr": 174
}
```
