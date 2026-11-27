---
title: "Task summary: Compress consistent multikey products for a formula verifier with tagged witness occurrences"
tags: [research-summary]
refs: [note:goal-e30dec5ceb4bf12756c8bfa37ac656e9185a83c224ed8b452446988fc9d1832b, theorem:AdvancedEncryption.WE.TagBank.linear_omission, theorem:AdvancedEncryption.WE.TagBank.rescale_error, theorem:AdvancedEncryption.WE.TagBank.switch_phase, theorem:AdvancedEncryption.WE.TagBank.tag_degree, theorem:AdvancedEncryption.WE.TagBank.uniform_view]
---

# Task summary: Compress consistent multikey products for a formula verifier with tagged witness occurrences

Task `8dd0dc49-2d23-4455-9e8c-c84d679429b8` (design / expand), goal `e30dec5ceb4bf12756c8bfa37ac656e9185a83c224ed8b452446988fc9d1832b`, outcome `verified_partial`. Mathematical status comes from the records, not from this note.

Five Lean solutions and two research notes establish the algebra of a one-layer tagged switch, mixed-modulus error accounting, and a local omission game with a fixed decisional LWE distribution. Source labels must be independent of the target challenge. The public local checker and the omitted-power prediction experiment do not establish joint authorization of hidden circuit wires. The dense scalar bodies alone require 6,878,586,381 bits. PR #171 continues the packed dictionary analysis. Full WE security and the registered clock remain open.

```sigaba-summary-v1
{
 "schema": "sigaba.summary.v1",
 "task_id": "8dd0dc49-2d23-4455-9e8c-c84d679429b8",
 "goal": "e30dec5ceb4bf12756c8bfa37ac656e9185a83c224ed8b452446988fc9d1832b",
 "outcome": "verified_partial",
 "pr": 168
}
```
