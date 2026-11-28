---
title: "Task summary: Build a shared-public-parameter wire pad generator from exact CBD Ring-LWE samples"
tags: [research-summary]
refs: [definition:WE_CBDWirePad, note:goal-e30dec5ceb4bf12756c8bfa37ac656e9185a83c224ed8b452446988fc9d1832b, theorem:AdvancedEncryption.WE.CBDWirePad.coefficient, theorem:AdvancedEncryption.WE.CBDWirePad.transport, theorem:AdvancedEncryption.WE.CBDWirePad.tree_capacity, theorem:AdvancedEncryption.WE.CBDWirePad.window_price]
---

# Task summary: Build a shared-public-parameter wire pad generator from exact CBD Ring-LWE samples

Task `f14b722b-4cd1-434a-af52-96cd05d89088` (design / deepen), goal `e30dec5ceb4bf12756c8bfa37ac656e9185a83c224ed8b452446988fc9d1832b`, outcome `verified_partial`. Mathematical status comes from the records, not from this note.

The shared-public-matrix generator uses exactly 4N fair seed bits and emits 8N packed bits. The registered CBD(1) coefficient law and the finite challenge conversion were checked, alongside two layout-specific counting lemmas. For independent full-width pads in the stated four-row construction and a single sequential full-width dictionary scan schedule, the 4096-gate issuer ledger is at least 4923756544. This count leaves alternative multiplication schedules open.

A complete bounded machine, the full quantum reduction for the garbling and its outer witness-encryption issuer, and an aggregate cost below 2^32 remain open.

```sigaba-summary-v1
{
 "schema": "sigaba.summary.v1",
 "task_id": "f14b722b-4cd1-434a-af52-96cd05d89088",
 "goal": "e30dec5ceb4bf12756c8bfa37ac656e9185a83c224ed8b452446988fc9d1832b",
 "outcome": "verified_partial",
 "pr": 152
}
```
