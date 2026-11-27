---
title: "Task summary: Instantiate nested string-output functions with dynamically bounded LWE FE and private function keys"
tags: [research-summary]
refs: [note:goal-e30dec5ceb4bf12756c8bfa37ac656e9185a83c224ed8b452446988fc9d1832b, theorem:AdvancedEncryption.WE.PrivateMIFE.native_ciphertext_rows, theorem:AdvancedEncryption.WE.PrivateMIFE.override_width]
---

# Task summary: Instantiate nested string-output functions with dynamically bounded LWE FE and private function keys

Task `078e8830-be2d-4f1b-841d-8dc027be84b7` (design / deepen), goal `e30dec5ceb4bf12756c8bfa37ac656e9185a83c224ed8b452446988fc9d1832b`, outcome `verified_partial`. Mathematical status comes from the records, not from this note.

The fixed-template native string-output construction uses the bounded AMVY ciphertext-policy FE transposition and BS private function encoding. For the serialized construction the adjacent slot widths force an explicit ciphertext-row cost; programmed child-key overrides also re-enter as private inputs. The two accepted Lean solutions certify the grouped arithmetic bound and the injectivity-based representation bound under their stated conditions.

For a known table the sender can generate the outer function-key outputs ahead of time and expose those child keys alongside the common encrypted suffix. The note gives the coupling with public postprocessing, including a per-side union bound and the extra cost to the reduction. This removes one outer layer. It leaves the actual price of the surviving child objects, full security under a concrete post-quantum registry instance and the strict aggregate machine budget open.

```sigaba-summary-v1
{
 "schema": "sigaba.summary.v1",
 "task_id": "078e8830-be2d-4f1b-841d-8dc027be84b7",
 "goal": "e30dec5ceb4bf12756c8bfa37ac656e9185a83c224ed8b452446988fc9d1832b",
 "outcome": "verified_partial",
 "pr": 141
}
```
