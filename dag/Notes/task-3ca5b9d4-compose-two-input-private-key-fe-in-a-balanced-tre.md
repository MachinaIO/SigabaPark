---
title: "Task summary: Compose two-input private-key FE in a balanced tree of ciphertext-producing functions"
tags: [research-summary]
refs: [note:goal-e30dec5ceb4bf12756c8bfa37ac656e9185a83c224ed8b452446988fc9d1832b, theorem:AdvancedEncryption.WE.FETree.collision_capacity, theorem:AdvancedEncryption.WE.FETree.exact_issuer_queries, theorem:AdvancedEncryption.WE.FETree.replica_floor]
---

# Task summary: Compose two-input private-key FE in a balanced tree of ciphertext-producing functions

Task `3ca5b9d4-2663-46f2-a7c4-11730797039e` (design / expand), goal `e30dec5ceb4bf12756c8bfa37ac656e9185a83c224ed8b452446988fc9d1832b`, outcome `verified_partial`. Mathematical status comes from the records, not from this note.

The balanced binary evaluator on sixteen 8-bit chunks publishes 4096 leaf ciphertexts and 15 internal function keys and takes 15 two-input evaluations on a witness. Child keys need to encapsulate the root issuer. Emulating an arbitrary deterministic issuer exactly from a finite black-box interface requires querying every address. For two balanced root halves this yields 2^65 responses for the literal full-table simulator; this is a proof cost. A native string-output instantiation and a reduction handling the complete correlated keys remain open.

The conditional lower bound on an independent one-bit replica implementation concerns honest output. For the specified equal-depth schedules and slot ciphertext overhead of at least eight bits, its leaf output is at least 4529848320 bits. The collision-capacity, replica, and exact-oracle-coverage lemmas are supported by complete accepted solutions. These constraints are specific to the stated implementations and interfaces.

```sigaba-summary-v1
{
 "schema": "sigaba.summary.v1",
 "task_id": "3ca5b9d4-2663-46f2-a7c4-11730797039e",
 "goal": "e30dec5ceb4bf12756c8bfa37ac656e9185a83c224ed8b452446988fc9d1832b",
 "outcome": "verified_partial",
 "pr": 140
}
```
