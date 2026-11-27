---
title: "Task summary: Lift the streamed XOR-lock circuit to a shallow trace predicate and cost honest trace generation"
tags: [research-summary]
refs: [definition:WE_TraceEmitter, definition:WE_TraceEmitterState, definition:WE_TraceEmitterStep, definition:WE_TraceLock, note:goal-e30dec5ceb4bf12756c8bfa37ac656e9185a83c224ed8b452446988fc9d1832b, theorem:AdvancedEncryption.WE.TraceEmitter.budget, theorem:AdvancedEncryption.WE.TraceEmitter.gate_replay, theorem:AdvancedEncryption.WE.TraceEmitter.load_registered, theorem:AdvancedEncryption.WE.TraceEmitter.run_registered, theorem:AdvancedEncryption.WE.TraceLock.check_shape]
---

# Task summary: Lift the streamed XOR-lock circuit to a shallow trace predicate and cost honest trace generation

Task `15018922-af98-4c39-99bb-75435a8eda44` (design / deepen), goal `e30dec5ceb4bf12756c8bfa37ac656e9185a83c224ed8b452446988fc9d1832b`, outcome `verified_partial`. Mathematical status comes from the records, not from this note.

The deterministic 26-state three-work-tape machine consumes the registered parameter, statement and witness fields and produces the framed sequence of all 4096 true gate values for every typed circuit and every ciphertext suffix. Its declared clock is 484513167 and its canonical machine description has length 88452, giving a component cost of 484601619. The run theorem uses the input adapter and gate replay lemmas supplied with this task.

The associated fixed-statement predicate checks a witness and a 4096-bit internal trace with 12288 two-input AND/XOR gates at depth at most 15. It accepts precisely a correct accepting trace under the registered circuit semantics. Wiring the emitter inside a full decryptor, compiling the actual lock with bounded resources, and establishing the complete quantum game are still open.

```sigaba-summary-v1
{
 "schema": "sigaba.summary.v1",
 "task_id": "15018922-af98-4c39-99bb-75435a8eda44",
 "goal": "e30dec5ceb4bf12756c8bfa37ac656e9185a83c224ed8b452446988fc9d1832b",
 "outcome": "verified_partial",
 "pr": 138
}
```
