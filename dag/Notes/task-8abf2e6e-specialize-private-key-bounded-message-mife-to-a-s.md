---
title: "Task summary: Specialize private-key bounded-message MIFE to a single circuit key and public witness chunks"
tags: [research-summary]
refs: [note:goal-e30dec5ceb4bf12756c8bfa37ac656e9185a83c224ed8b452446988fc9d1832b, theorem:AdvancedEncryption.WE.PrivateMIFE.full_table_admissibility, theorem:AdvancedEncryption.WE.PrivateMIFE.literal_dec_calls, theorem:AdvancedEncryption.WE.PrivateMIFE.literal_site_floor, theorem:AdvancedEncryption.WE.PrivateMIFE.serial_key_floor]
---

# Task summary: Specialize private-key bounded-message MIFE to a single circuit key and public witness chunks

Task `8abf2e6e-3f0c-472c-a849-1474725dc383` (design / expand), goal `e30dec5ceb4bf12756c8bfa37ac656e9185a83c224ed8b452446988fc9d1832b`, outcome `verified_partial`. Mathematical status comes from the records, not from this note.

For private function-hiding MIFE, fold the message bit into the single function key. All combinations of the published witness-chunk ciphertexts give equal function outputs on an unsatisfiable circuit. For the literal serial BKS selective scheme the exact number of base decryptions is 2^k-1 for k slots. Combined with the count of physically separate base ciphertexts and functional keys, this gives the attained 31744-site frontier at both 13 and 14 slots. These are object and operation counts, not Turing-machine clocks.

A fixed-width bit-parallel single-output implementation with keys at least 128 bits long cannot meet the strict 2^32 budget for any chunk partition or public prefix length. The notes also derive an 84-bit threshold under the specified public-output model. This is an implementation-specific constraint. The scheme still needs an efficient native string-output base, a concrete quantum reduction with all correlated public fields and a complete machine budget. Follow-ups on native keys and the precise starred-master hybrid are separate tasks.

```sigaba-summary-v1
{
 "schema": "sigaba.summary.v1",
 "task_id": "8abf2e6e-3f0c-472c-a849-1474725dc383",
 "goal": "e30dec5ceb4bf12756c8bfa37ac656e9185a83c224ed8b452446988fc9d1832b",
 "outcome": "verified_partial",
 "pr": 139
}
```
