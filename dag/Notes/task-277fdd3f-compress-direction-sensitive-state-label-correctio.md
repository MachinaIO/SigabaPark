---
title: "Task summary: Compress direction-sensitive state-label corrections for the read-once energy verifier"
tags: [research-summary]
refs: [note:goal-e30dec5ceb4bf12756c8bfa37ac656e9185a83c224ed8b452446988fc9d1832b, theorem:AdvancedEncryption.WE.DirectedLabels.additive_view, theorem:AdvancedEncryption.WE.DirectedLabels.chart_record, theorem:AdvancedEncryption.WE.DirectedLabels.decoding_error, theorem:AdvancedEncryption.WE.DirectedLabels.essential_injective, theorem:AdvancedEncryption.WE.DirectedLabels.extension_representation, theorem:AdvancedEncryption.WE.DirectedLabels.interval_overlap, theorem:AdvancedEncryption.WE.DirectedLabels.point_gap, theorem:AdvancedEncryption.WE.DirectedLabels.subset_sum_size]
---

# Task summary: Compress direction-sensitive state-label corrections for the read-once energy verifier

Task `277fdd3f-0954-4ca7-9f9e-a5c0e5729024` (design / expand), goal `e30dec5ceb4bf12756c8bfa37ac656e9185a83c224ed8b452446988fc9d1832b`, outcome `verified_partial`. Mathematical status comes from the records, not from this note.

The task analyzes joint privacy of directed state labels and proposes contracting a bounded verifier suffix into one shift-hiding key with boundary deliveries. For the flat all-domain sampled-dictionary variant, a known single accepting input yields a quantitative incompatibility: unless the sampler hits such an input, the published dictionary can be simulated in both shift worlds, and an efficient correct decoder for that input would distinguish the shift. The eight local Lean proofs were accepted by the official gate, including the finite chart, error and distinguishing inequalities. The PS instantiation, tight finite parameters and complete quantum-security reduction for bounded suffix delivery, and a full low-cost WE remain open.

```sigaba-summary-v1
{
 "schema": "sigaba.summary.v1",
 "task_id": "277fdd3f-0954-4ca7-9f9e-a5c0e5729024",
 "goal": "e30dec5ceb4bf12756c8bfa37ac656e9185a83c224ed8b452446988fc9d1832b",
 "outcome": "verified_partial",
 "pr": 166
}
```
