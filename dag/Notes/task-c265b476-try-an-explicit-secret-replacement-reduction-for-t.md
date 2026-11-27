---
title: "Task summary: Try an explicit secret-replacement reduction for the streamed encrypted-lock header"
tags: [research-summary]
refs: [note:goal-e30dec5ceb4bf12756c8bfa37ac656e9185a83c224ed8b452446988fc9d1832b, theorem:AdvancedEncryption.WE.LockHeader.completion_budget, theorem:AdvancedEncryption.WE.LockHeader.completion_count, theorem:AdvancedEncryption.WE.LockHeader.yes_fixture_simulator_floor]
---

# Task summary: Try an explicit secret-replacement reduction for the streamed encrypted-lock header

Task `c265b476-c26c-481e-976e-27748a6c4ddd` (design / deepen), goal `e30dec5ceb4bf12756c8bfa37ac656e9185a83c224ed8b452446988fc9d1832b`, outcome `verified_partial`. Mathematical status comes from the records, not from this note.

The exported XOR header in PR 131 correlates the comparison lock with the program key. Checking a transcript inside the locked predicate can enforce evaluation provenance. This check leaves the raw secret decryption key and the encrypted source in the simulator's conditioning data. An independent-lock proof still needs a separate joint-distribution argument.

If the header withholds s uniform bits, classical completion testing at an honest witness requires q >= (1-2^-127) 2^s equality queries to meet correctness for both payloads. AdvancedEncryption.WE.LockHeader.completion_count and completion_budget give the finite counting and strict-budget consequences. This excludes s >= 32 for this particular completion decoder. The public-YES simulator lemma yes_fixture_simulator_floor gives a second test: at least one of two correct real payload distributions is separated from any common simulator by at least 1/2 minus the correctness error under the honest-decoding observation. The same quantitative simulation claim cannot be applied solely on an entropy criterion that also holds on a known satisfiable fixture. A fixed-assumption reduction valid for all false statements and a complete WE implementation under 2^32 remain open.

```sigaba-summary-v1
{
 "schema": "sigaba.summary.v1",
 "task_id": "c265b476-c26c-481e-976e-27748a6c4ddd",
 "goal": "e30dec5ceb4bf12756c8bfa37ac656e9185a83c224ed8b452446988fc9d1832b",
 "outcome": "verified_partial",
 "pr": 134
}
```
