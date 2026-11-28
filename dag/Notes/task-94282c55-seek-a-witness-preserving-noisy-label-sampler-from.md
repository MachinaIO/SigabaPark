---
title: "Task summary: Seek a witness-preserving noisy-label sampler from a fixed post-quantum challenge"
tags: [research-summary]
refs: [definition:BucketLabel, note:goal-e30dec5ceb4bf12756c8bfa37ac656e9185a83c224ed8b452446988fc9d1832b, theorem:AdvancedEncryption.WE.BucketLabel.authorized, theorem:AdvancedEncryption.WE.BucketLabel.hybridSquared, theorem:AdvancedEncryption.WE.BucketLabel.idealCoupling, theorem:AdvancedEncryption.WE.BucketLabel.predictorGap, theorem:AdvancedEncryption.WE.BucketLabel.publicMasks, theorem:AdvancedEncryption.WE.BucketLabel.rowSmallBall]
---

# Task summary: Seek a witness-preserving noisy-label sampler from a fixed post-quantum challenge

Task `94282c55-a44d-4e5f-b48b-068a82b034b3` (design / expand), goal `e30dec5ceb4bf12756c8bfa37ac656e9185a83c224ed8b452446988fc9d1832b`, outcome `verified_partial`. Mathematical status comes from the records, not from this note.

For the fixed decision-LWE challenge at n=1024, q=64 and 753 rows, the bucket issuer hides the bit on a false common-tag statement in the uniform hybrid. A witness reconstructs from its sixteen selected shares. The six component proofs and the note passed the official gate. Quantum source hardness, a coupled end-to-end machine proof and unrestricted circuit coverage remain open.

```sigaba-summary-v1
{
 "schema": "sigaba.summary.v1",
 "task_id": "94282c55-a44d-4e5f-b48b-068a82b034b3",
 "goal": "e30dec5ceb4bf12756c8bfa37ac656e9185a83c224ed8b452446988fc9d1832b",
 "outcome": "verified_partial",
 "pr": 251
}
```
