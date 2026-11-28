---
title: "Task summary: Compile two independently selectable bounded trace vectors to one witness-gated inner product"
tags: [research-summary]
refs: [definition:TwoTraceEnergy, note:goal-e30dec5ceb4bf12756c8bfa37ac656e9185a83c224ed8b452446988fc9d1832b, theorem:TwoTraceEnergy.independentTrace, theorem:TwoTraceEnergy.integerCorrection, theorem:TwoTraceEnergy.registeredRun]
---

# Task summary: Compile two independently selectable bounded trace vectors to one witness-gated inner product

Task `aa211652-b67f-4f2d-8887-1a932c57c24e` (design / expand), goal `e30dec5ceb4bf12756c8bfa37ac656e9185a83c224ed8b452446988fc9d1832b`, outcome `verified_partial`. Mathematical status comes from the records, not from this note.

The verified construction gives a two-trace energy predicate for capped NAND evaluation. Its zero set on Boolean traces characterizes joint consistency and acceptance. The registered-run theorem and integer-correction lemmas certify parts of the deterministic checker. The 15-file checkpoint includes three accepted Lean solutions and the DAG note. The predicate still needs a compact cryptographic release that exposes only the authorized payload, complete false-instance simulation from a statement-independent post-quantum assumption, and the full registered cost below 2^32.

```sigaba-summary-v1
{
 "schema": "sigaba.summary.v1",
 "task_id": "aa211652-b67f-4f2d-8887-1a932c57c24e",
 "goal": "e30dec5ceb4bf12756c8bfa37ac656e9185a83c224ed8b452446988fc9d1832b",
 "outcome": "verified_partial",
 "pr": 226
}
```
