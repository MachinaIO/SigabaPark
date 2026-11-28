---
title: "Task summary: Certify witness density and batch public CircuitSAT trials on sequential tapes"
tags: [research-summary]
refs: [definition:DensityTrials, note:goal-e30dec5ceb4bf12756c8bfa37ac656e9185a83c224ed8b452446988fc9d1832b, theorem:AdvancedEncryption.WE.DensityTrials.batch_lane, theorem:AdvancedEncryption.WE.DensityTrials.fair_error_count, theorem:AdvancedEncryption.WE.DensityTrials.minimal_coefficient, theorem:AdvancedEncryption.WE.DensityTrials.minimum_weight, theorem:AdvancedEncryption.WE.DensityTrials.trial_bound]
---

# Task summary: Certify witness density and batch public CircuitSAT trials on sequential tapes

Task `23ecda1e-56e6-46c9-9cdb-ffe09cc564b2` (design / expand), goal `e30dec5ceb4bf12756c8bfa37ac656e9185a83c224ed8b452446988fc9d1832b`, outcome `verified_partial`. Mathematical status comes from the records, not from this note.

Point-specific low-degree cut certificates bound the satisfying density. A minimum-support coefficient outside the rejecting-row span yields an actual witness of Hamming weight at most the degree bound. With full coverage, exhaustion proves unsatisfiability. At degree two, 306 independent trials and a fair fallback bit give error at most 2^-128 and identical false-instance distributions. The all-topology lane evaluator has a partial 403767321 data-cell traversal ledger. Five proof solutions cover the algebra, sampling, and lane semantics; the full machine clocks, descriptions and an all-input WE remain open.

```sigaba-summary-v1
{
 "schema": "sigaba.summary.v1",
 "task_id": "23ecda1e-56e6-46c9-9cdb-ffe09cc564b2",
 "goal": "e30dec5ceb4bf12756c8bfa37ac656e9185a83c224ed8b452446988fc9d1832b",
 "outcome": "verified_partial",
 "pr": 160
}
```
