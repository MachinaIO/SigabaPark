---
title: "Task summary: Specialize published oblivious and succinct LWE sampling to a one-bit null-circuit release"
tags: [research-summary]
refs: [definition:NullSamplerCosts, note:goal-e30dec5ceb4bf12756c8bfa37ac656e9185a83c224ed8b452446988fc9d1832b, theorem:AdvancedEncryption.WE.NullSampler.coordinateCode, theorem:AdvancedEncryption.WE.NullSampler.fullHeader, theorem:AdvancedEncryption.WE.NullSampler.groupedCost, theorem:AdvancedEncryption.WE.NullSampler.observableCompression, theorem:AdvancedEncryption.WE.NullSampler.sharedCRS, theorem:AdvancedEncryption.WE.NullSampler.sparseQueries]
---

# Task summary: Specialize published oblivious and succinct LWE sampling to a one-bit null-circuit release

Task `6a5ade30-0d1f-4eb6-aada-0438bda3c28b` (design / expand), goal `e30dec5ceb4bf12756c8bfa37ac656e9185a83c224ed8b452446988fc9d1832b`, outcome `verified_partial`. Mathematical status comes from the records, not from this note.

For a public NAND function the private SRE input can consist of the one-bit payload. Counting the fields in the analyzed literal shared-CRS WW construction still gives over 2^100 raw bits. The published DQ tensor opening in the covered balanced decompositions requires at least 2^120 entries. The counts apply to those implementations. They leave adaptive preprocessing, selective evaluation, alternative succinct representations and the general WE cost bound open.

```sigaba-summary-v1
{
 "schema": "sigaba.summary.v1",
 "task_id": "6a5ade30-0d1f-4eb6-aada-0438bda3c28b",
 "goal": "e30dec5ceb4bf12756c8bfa37ac656e9185a83c224ed8b452446988fc9d1832b",
 "outcome": "verified_partial",
 "pr": 242
}
```
