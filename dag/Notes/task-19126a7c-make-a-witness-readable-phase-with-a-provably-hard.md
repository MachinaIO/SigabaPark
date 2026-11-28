---
title: "Task summary: Make a witness-readable phase with a provably hard average conditional RingLWE header"
tags: [research-summary]
refs: [definition:ConjugatePhaseGrant, definition:PrefixCommonInformation, definition:PrefixSamplerTest, definition:PrefixWalkGrant, definition:RingPrefixArithmetic, note:goal-e30dec5ceb4bf12756c8bfa37ac656e9185a83c224ed8b452446988fc9d1832b]
---

# Task summary: Make a witness-readable phase with a provably hard average conditional RingLWE header

Task `19126a7c-587e-498e-81b5-3c11719de326` (design / expand), goal `e30dec5ceb4bf12756c8bfa37ac656e9185a83c224ed8b452446988fc9d1832b`, outcome `verified_partial`. Mathematical status comes from the records, not from this note.

The corrected PrefixCommonInformation definition and four companion definitions passed the official gate. The half-prefix construction uses up to 511 preceding coefficients and gives a collision lower bound of 1/9 within 29,192 raw capsule bits. The positive witness grants recover an actual phase of the fixed Ring-LWE challenge on the stated affine-route or graph classes, with joint simulation on false instances of those classes. A general NAND witness grant, the quantified quantum security losses, and the registered total-machine cost remain open.

```sigaba-summary-v1
{
 "schema": "sigaba.summary.v1",
 "task_id": "19126a7c-587e-498e-81b5-3c11719de326",
 "goal": "e30dec5ceb4bf12756c8bfa37ac656e9185a83c224ed8b452446988fc9d1832b",
 "outcome": "verified_partial",
 "pr": 244
}
```
