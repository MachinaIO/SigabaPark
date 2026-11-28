---
title: "Task summary: Read each claimed trace bit once when computing the complete quadratic NAND energy"
tags: [research-summary]
refs: [definition:WE_OnceTraceScan, note:goal-e30dec5ceb4bf12756c8bfa37ac656e9185a83c224ed8b452446988fc9d1832b, theorem:AdvancedEncryption.WE.OnceEnergy.moment_endpoint, theorem:AdvancedEncryption.WE.OnceEnergy.ordered_pairs, theorem:AdvancedEncryption.WE.OnceEnergy.public_group_direction, theorem:AdvancedEncryption.WE.OnceEnergy.quadratic_and_bounded, theorem:AdvancedEncryption.WE.OnceEnergy.two_trace_endpoint, theorem:AdvancedEncryption.WE.OnceEnergy.zero_iff_registered]
---

# Task summary: Read each claimed trace bit once when computing the complete quadratic NAND energy

Task `a2f83af6-5e48-46bb-80a8-8454731ad2b6` (design / deepen), goal `e30dec5ceb4bf12756c8bfa37ac656e9185a83c224ed8b452446988fc9d1832b`, outcome `verified_partial`. Mathematical status comes from the records, not from this note.

Six accepted Lean proofs cover the registered NAND trace predicate, its bounded quadratic energy, a one-pass scan, and limits of affine terminal openings. A zero-energy trace exists exactly for an accepting registered input. For a false all-live circuit, an exposed affine zero-energy terminal can also accept an affine combination of two reachable endpoint states. The sparse coefficient layout takes at most 550670 bits; it neither authenticates reachability nor establishes an encryption scheme or a full machine cost. The order-independent Cayley analysis belongs to a separate successor task.

```sigaba-summary-v1
{
 "schema": "sigaba.summary.v1",
 "task_id": "a2f83af6-5e48-46bb-80a8-8454731ad2b6",
 "goal": "e30dec5ceb4bf12756c8bfa37ac656e9185a83c224ed8b452446988fc9d1832b",
 "outcome": "verified_partial",
 "pr": 165
}
```
