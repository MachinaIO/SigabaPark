---
title: "Task summary: Move the terminal witness chunk into a scoped public encryption algorithm"
tags: [research-summary]
refs: [note:goal-e30dec5ceb4bf12756c8bfa37ac656e9185a83c224ed8b452446988fc9d1832b, theorem:AdvancedEncryption.WE.PublicTail.cofactor_gate, theorem:AdvancedEncryption.WE.PublicTail.dictionary_criterion, theorem:AdvancedEncryption.WE.PublicTail.literal_projection_horizon, theorem:AdvancedEncryption.WE.PublicTail.marker_capacity]
---

# Task summary: Move the terminal witness chunk into a scoped public encryption algorithm

Task `ec363428-0968-4938-9248-8ce56f8eda1c` (design / expand), goal `e30dec5ceb4bf12756c8bfa37ac656e9185a83c224ed8b452446988fc9d1832b`, outcome `verified_partial`. Mathematical status comes from the records, not from this note.

For a split witness (p,u), replacing a private predicate by beta AND (there exists v with phi(p,v)) eliminates the public terminal ciphertext table. On a valid witness the private predicate returns beta. If exact evaluation is desired for every pair, apply the public phi(p,u) check to the result. For every false statement the two projected private functions agree on the whole prefix domain.

The projected circuit must still be generated and evaluated. Literal cofactor duplication grows exponentially in the number of removed bits, and the stated rank-four layouts cannot pay for both the front fields and the required ordinary garbling in the tested parameter regimes. The alternative scoped-generator approach also needs consistency of the exact returned bytes in its FE hybrids; a finite table can repair equality at the price of retaining its contents. Secret correlations, physical costs of more compact projectors, and a registered post-quantum WE implementation remain open.

```sigaba-summary-v1
{
 "schema": "sigaba.summary.v1",
 "task_id": "ec363428-0968-4938-9248-8ce56f8eda1c",
 "goal": "e30dec5ceb4bf12756c8bfa37ac656e9185a83c224ed8b452446988fc9d1832b",
 "outcome": "verified_partial",
 "pr": 148
}
```
