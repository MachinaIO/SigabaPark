---
title: "Task summary: Compile the two-join key router with one fixed expansion per vertex and an explicit multi-tape clock"
tags: [research-summary]
refs: [definition:StreamedRouterBlock, note:goal-e30dec5ceb4bf12756c8bfa37ac656e9185a83c224ed8b452446988fc9d1832b, theorem:AdvancedEncryption.WE.StreamRouter.block_cost, theorem:AdvancedEncryption.WE.StreamRouter.hidden_terminal, theorem:AdvancedEncryption.WE.StreamRouter.packet_budget]
---

# Task summary: Compile the two-join key router with one fixed expansion per vertex and an explicit multi-tape clock

Task `bf96e931-ca06-4464-a562-ed6c7fc39c4a` (design / deepen), goal `e30dec5ceb4bf12756c8bfa37ac656e9185a83c224ed8b452446988fc9d1832b`, outcome `verified_partial`. Mathematical status comes from the records, not from this note.

Two explicit five-tape ChaCha20 machines and three component solutions passed the final controller snapshot. The static-source two-join router uses 33,788 block evaluations and 12,972,033 router bits before source openings. Sharing the quarter-round code reduces the generator description. The outer controller still lacks a certified full cost below 2^32 and the static source supplier requires witness-dependent authorization before it can serve a general circuit. A one-block hardness conjecture is being defined and reviewed separately, in PRs 178 and 179.

```sigaba-summary-v1
{
 "schema": "sigaba.summary.v1",
 "task_id": "bf96e931-ca06-4464-a562-ed6c7fc39c4a",
 "goal": "e30dec5ceb4bf12756c8bfa37ac656e9185a83c224ed8b452446988fc9d1832b",
 "outcome": "verified_partial",
 "pr": 173
}
```
