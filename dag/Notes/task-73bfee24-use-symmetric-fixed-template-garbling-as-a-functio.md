---
title: "Task summary: Use symmetric fixed-template garbling as a function-private native string-output base"
tags: [research-summary]
refs: [note:goal-e30dec5ceb4bf12756c8bfa37ac656e9185a83c224ed8b452446988fc9d1832b, theorem:AdvancedEncryption.WE.PrivateMIFE.terminal_ciphertext_composition, theorem:AdvancedEncryption.WE.PrivateMIFE.terminal_ciphertext_floor]
---

# Task summary: Use symmetric fixed-template garbling as a function-private native string-output base

Task `73bfee24-6e49-4e4b-9753-befbb9bd9e15` (design / deepen), goal `e30dec5ceb4bf12756c8bfa37ac656e9185a83c224ed8b452446988fc9d1832b`, outcome `verified_partial`. Mathematical status comes from the records, not from this note.

For a fixed batch of independent function-private garblings, a slot key can generate the selected parameter labels directly. The native garbling note accounts separately for ciphertext-side message labels and for the ordinary computation that produces the output. In the stated literal BKS input encoding, an arity-r terminal ciphertext has width at least w^(2^(r-1)) s, for input-label width w and initial width s. With w at least 16, the resulting explicit tables cannot meet the strict 2^32 bound for any partition of the 128 witness bits under the note's hypotheses.

The supplementary selector note describes a finite guessing loss for adaptive slot queries and a fixed-batch scheduling argument for the designated BKS comparisons. These arguments require the stated admissibility and independence conditions. A quantitative reduction to registered post-quantum assumptions and a complete WE machine remain open.

```sigaba-summary-v1
{
 "schema": "sigaba.summary.v1",
 "task_id": "73bfee24-6e49-4e4b-9753-befbb9bd9e15",
 "goal": "e30dec5ceb4bf12756c8bfa37ac656e9185a83c224ed8b452446988fc9d1832b",
 "outcome": "verified_partial",
 "pr": 144
}
```
