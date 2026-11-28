---
title: "Task summary: Evaluate a fixed related-key pad assumption for source-label garbling and its one-bank hybrid"
tags: [research-summary]
refs: [note:goal-e30dec5ceb4bf12756c8bfa37ac656e9185a83c224ed8b452446988fc9d1832b, theorem:AdvancedEncryption.WE.SourcePads.absolute_counts, theorem:AdvancedEncryption.WE.SourcePads.bank_injective, theorem:AdvancedEncryption.WE.SourcePads.centered_counts, theorem:AdvancedEncryption.WE.SourcePads.unique_collision]
---

# Task summary: Evaluate a fixed related-key pad assumption for source-label garbling and its one-bank hybrid

Task `87cfdde9-36f6-4a0a-8eaa-8f989b4c3509` (design / expand), goal `e30dec5ceb4bf12756c8bfa37ac656e9185a83c224ed8b452446988fc9d1832b`, outcome `verified_partial`. Mathematical status comes from the records, not from this note.

Four accepted Lean solutions establish finite counting and injectivity lemmas. The note derives a joint selected-input simulator for two NAND gates including the true intermediate payload and identifies a fixed, circuit-independent rounded projection game. For its displayed expanded-root parameters the statistical two-gate bound is below 2^-131. General initialization and terminal consistency, numerical QPT strength and full WE cost remain open. PR 174 independently studies the fixed pad hypothesis. This task does not establish Ideal Cipher Annihilation Security of ePrint 2020/1502.

```sigaba-summary-v1
{
 "schema": "sigaba.summary.v1",
 "task_id": "87cfdde9-36f6-4a0a-8eaa-8f989b4c3509",
 "goal": "e30dec5ceb4bf12756c8bfa37ac656e9185a83c224ed8b452446988fc9d1832b",
 "outcome": "verified_partial",
 "pr": 170
}
```
