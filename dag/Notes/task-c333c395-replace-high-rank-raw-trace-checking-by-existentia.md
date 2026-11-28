---
title: "Task summary: Replace high-rank raw trace checking by existentially transparent circuit resynthesis"
tags: [research-summary]
refs: [note:goal-e30dec5ceb4bf12756c8bfa37ac656e9185a83c224ed8b452446988fc9d1832b, theorem:AdvancedEncryption.WE.TraceProject.anf_descent, theorem:AdvancedEncryption.WE.TraceProject.cayley_certificate, theorem:AdvancedEncryption.WE.TraceProject.chart_projection, theorem:AdvancedEncryption.WE.TraceProject.cube_descent, theorem:AdvancedEncryption.WE.TraceProject.support_union, theorem:AdvancedEncryption.WE.TraceProject.triangular_profiles]
---

# Task summary: Replace high-rank raw trace checking by existentially transparent circuit resynthesis

Task `c333c395-b578-4cb1-9bcf-be17ccd72b0e` (design / deepen), goal `e30dec5ceb4bf12756c8bfa37ac656e9185a83c224ed8b452446988fc9d1832b`, outcome `verified_partial`. Mathematical status comes from the records, not from this note.

For a concrete all-live 4096-NAND family, the exact trace relation has an order-independent rank obstruction. The graph uses a 21-regular Cayley construction and the matched input cut yields a triangular submatrix of rank 2^45. The result concerns one-pass trace representations. The separate positive compiler preserves the attainable joint output profiles of a selected private block with sparse witnesses, including shared-variable monotone terms and bounded-degree Boolean outputs. In two replayed full-size instances the reduced circuits use 8 variables with 46 or 39 live gates, and all 256 residual assignments were checked. A further family retains an arbitrary 2500-gate residual on 64 variables. Six Lean proof solutions were accepted; the full graph and compiler composition also uses the arguments and replay in the notes. This does not establish universal compression or the full registered WE cost.

```sigaba-summary-v1
{
 "schema": "sigaba.summary.v1",
 "task_id": "c333c395-b578-4cb1-9bcf-be17ccd72b0e",
 "goal": "e30dec5ceb4bf12756c8bfa37ac656e9185a83c224ed8b452446988fc9d1832b",
 "outcome": "verified_partial",
 "pr": 167
}
```
