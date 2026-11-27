---
title: "Task summary: Bind signed tag moments to encrypted gate provenance across two successive joins"
tags: [research-summary]
refs: [note:goal-e30dec5ceb4bf12756c8bfa37ac656e9185a83c224ed8b452446988fc9d1832b, theorem:AdvancedEncryption.WE.JoinRoute.hidden_incidence_frame, theorem:AdvancedEncryption.WE.JoinRoute.opened_native_source, theorem:AdvancedEncryption.WE.JoinRoute.overlap_coefficient, theorem:AdvancedEncryption.WE.JoinRoute.public_check_image, theorem:AdvancedEncryption.WE.JoinRoute.signed_three, theorem:AdvancedEncryption.WE.JoinRoute.two_join_closure]
---

# Task summary: Bind signed tag moments to encrypted gate provenance across two successive joins

Task `d8ba7da1-9796-476f-980e-02f537918ff1` (design / deepen), goal `e30dec5ceb4bf12756c8bfa37ac656e9185a83c224ed8b452446988fc9d1832b`, outcome `verified_partial`. Mathematical status comes from the records, not from this note.

The static-source two-join range router separates graph reachability from native hidden-wire authorization. Its source keys are independent. At 4,224 tags the explicit graph has 33,776 degree-two vertices, twelve degree-one vertices, and one terminal. The note and replay cover 4,672 static source subsets, and six Lean solutions passed. The original dense implementation misses the budget. A leaner message-only compiler is studied separately in PR #173. Connecting the router to native same-root hidden wire openings for all circuits, and certifying a total cost below 2^32, remain open.

```sigaba-summary-v1
{
 "schema": "sigaba.summary.v1",
 "task_id": "d8ba7da1-9796-476f-980e-02f537918ff1",
 "goal": "e30dec5ceb4bf12756c8bfa37ac656e9185a83c224ed8b452446988fc9d1832b",
 "outcome": "verified_partial",
 "pr": 169
}
```
