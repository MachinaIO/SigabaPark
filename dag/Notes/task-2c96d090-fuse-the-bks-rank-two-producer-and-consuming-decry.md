---
title: "Task summary: Fuse the BKS rank-two producer and consuming decryption with explicit private interfaces"
tags: [research-summary]
refs: [note:goal-e30dec5ceb4bf12756c8bfa37ac656e9185a83c224ed8b452446988fc9d1832b, theorem:AdvancedEncryption.WE.FusedRank.joint_coverage, theorem:AdvancedEncryption.WE.FusedRank.one_key_frame_fibers, theorem:AdvancedEncryption.WE.FusedRank.public_consumer, theorem:AdvancedEncryption.WE.FusedRank.row_reindex, theorem:AdvancedEncryption.WE.FusedRank.triangular_frame]
---

# Task summary: Fuse the BKS rank-two producer and consuming decryption with explicit private interfaces

Task `2c96d090-5c33-4006-85d0-b4cb744176d6` (design / expand), goal `e30dec5ceb4bf12756c8bfa37ac656e9185a83c224ed8b452446988fc9d1832b`, outcome `verified_partial`. Mathematical status comes from the records, not from this note.

With one hidden scalar function key and fixed public slot counts, the triangular-frame construction realizes beta times the inner product of two private feature vectors. A finite bijection proves equality of the full public records for equal output matrices. For two slots per side and eight-bit local vectors, the layout uses 141 public bits and 138 independent setup bits. The separate row-reindexing result specifies when public postprocessing of one child suffices and which joint Cartesian comparisons require protection.

Issuing both scalar keys on the same setup exposes their equality even when every output vanishes. A compiler mapping the recursive private producer and consumer for general registered NAND circuits into these local features, a concrete complete cost below 2^32 and the quantum WE security argument remain open.

```sigaba-summary-v1
{
 "schema": "sigaba.summary.v1",
 "task_id": "2c96d090-5c33-4006-85d0-b4cb744176d6",
 "goal": "e30dec5ceb4bf12756c8bfa37ac656e9185a83c224ed8b452446988fc9d1832b",
 "outcome": "verified_partial",
 "pr": 151
}
```
