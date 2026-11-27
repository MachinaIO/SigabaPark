---
title: "Task summary: Instantiate one-bit-per-gate lattice garbling for fixed-template witness encryption"
tags: [research-summary]
refs: [note:goal-e30dec5ceb4bf12756c8bfa37ac656e9185a83c224ed8b452446988fc9d1832b, theorem:AdvancedEncryption.WE.BitGC.mixed_shift, theorem:AdvancedEncryption.WE.BitGC.nand_mixed_unit, theorem:AdvancedEncryption.WE.BitGC.seed_bank_floor]
---

# Task summary: Instantiate one-bit-per-gate lattice garbling for fixed-template witness encryption

Task `c3db738d-3a12-4964-b06d-ebfd84d9529a` (design / expand), goal `e30dec5ceb4bf12756c8bfa37ac656e9185a83c224ed8b452446988fc9d1832b`, outcome `verified_partial`. Mathematical status comes from the records, not from this note.

Replacing the encrypted PRG seed with independently encrypted wire masks removes homomorphic PRG evaluation from the single-use BitGC candidate and increases the number of mask ciphertexts. The masked NAND retains a nonzero mixed coefficient under every input mask. The original uncompressed encrypted seed alone occupies at least 2^32 bits when the seed length is at least 128, the ring degree is at least 512 and the gadget width parameter ell is at least 128.

The source uses cross-key switches and a joint conversion hint with shared bases and a two-secret product. Its distribution is not directly supplied by the registered single-secret automorphism-key family. The mixed-difference identity excludes a separable affine match of the product shift. A quantitative quantum reduction for the joint public view, finite correctness and complete running-time bounds remain open.

```sigaba-summary-v1
{
 "schema": "sigaba.summary.v1",
 "task_id": "c3db738d-3a12-4964-b06d-ebfd84d9529a",
 "goal": "e30dec5ceb4bf12756c8bfa37ac656e9185a83c224ed8b452446988fc9d1832b",
 "outcome": "verified_partial",
 "pr": 147
}
```
