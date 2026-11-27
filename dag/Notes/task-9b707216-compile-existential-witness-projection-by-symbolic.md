---
title: "Task summary: Compile existential witness projection by symbolic bucket elimination before private evaluation"
tags: [research-summary]
refs: [note:goal-e30dec5ceb4bf12756c8bfa37ac656e9185a83c224ed8b452446988fc9d1832b, theorem:AdvancedEncryption.WE.SymbolicBucket.cut_image, theorem:AdvancedEncryption.WE.SymbolicBucket.step]
---

# Task summary: Compile existential witness projection by symbolic bucket elimination before private evaluation

Task `9b707216-229c-4c16-bde3-a5553839c574` (design / deepen), goal `e30dec5ceb4bf12756c8bfa37ac656e9185a83c224ed8b452446988fc9d1832b`, outcome `verified_partial`. Mathematical status comes from the records, not from this note.

Symbolic bucket elimination treats the unprojected front inputs as circuit literals. Joining the factors using one existential variable and disjoining its two slices preserves the projected predicate at each remaining assignment. The compiler normalizes the registered forward-read convention, retains expression sharing and falls back to direct exact projection when its work cap is reached.

On the documented 4,096-gate example with thirteen tail bits, elimination used width three and 24,591 table cells and emitted two NAND gates. A second instance retained a 500-gate front predicate. Independent replay reproduced both results and the small exhaustive comparisons. A six-clique family obstructs the stated width cap for sixty-four tail variables. The measurements do not bound the cost of compiling every circuit, issuing the private evaluator or completing the registered quantum security proof.

```sigaba-summary-v1
{
 "schema": "sigaba.summary.v1",
 "task_id": "9b707216-229c-4c16-bde3-a5553839c574",
 "goal": "e30dec5ceb4bf12756c8bfa37ac656e9185a83c224ed8b452446988fc9d1832b",
 "outcome": "verified_partial",
 "pr": 149
}
```
