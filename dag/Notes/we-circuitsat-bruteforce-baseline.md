---
title: Brute-force WE for NAND-circuit SAT - an assumption-free baseline, not a construction
refs: [definition:WE_CircuitSAT, definition:WE_CircuitSAT_Impl_BruteForce, theorem:AdvancedEncryption.WE.CircuitSAT.BruteForce.submissionProp]
tags: [witness-encryption, baseline, submission]
---
`AdvancedEncryption.WE.CircuitSAT.BruteForce.u` is a submission for `WE_CircuitSAT` whose
Submission proposition holds **with no premises**: `Enc(phi, beta)` decides whether the circuit
`phi` is satisfiable and outputs `[beta]` if so and `[false]` otherwise; `Dec` outputs the
ciphertext. Correctness is exact, and for an unsatisfiable `phi` both encryptions are the same
word, so every adversary has advantage 0.

This is a **baseline, not a real construction**. As the note of `Def_WE` says, at fixed
parameters `Enc` can always decide the language by brute force; a submission is only meaningful
at a cost far below that.

**What `N` is.** The machines come from `Machine.exists_finiteAlg_det` (via `AlmostConst`): they
exist because the valid inputs form a finite set, and are in effect hard-wired tables over all
circuits, i.e. of the order of `2^{|phi|}` entries, with `|phi|` the encoded length of a circuit
(each of the `2^12` gates holds two unary wire indices up to `2^12 + 129`, so up to tens of millions of bits). The claimed cost is `N := WE.cost impl`, the cost of these
machines: it is **not an explicit number**, and it is astronomically larger than any meaningful
construction. Its role is only to record that `Spec P R` is satisfiable without assumptions.

**Towards an explicit cost.** An exhaustive-search `Enc` costs about `2^128` circuit evaluations
of `2^12` gates each, so roughly `2^140` times a per-gate overhead on a Turing machine (wire
lookup in a list of up to `2^12 + 129` wires: a further factor of order `2^12` to `2^24` with
unary indices). An explicit bound needs a tape program (`Prog`/`XProg` compiled with
`toMachineT`, with `time_*`/`descLen_*` lemmas) that (1) parses the input tuple and the gate list
in the `encGates` format, (2) runs a 128-bit counter over all assignments, (3) evaluates
`evalGates` on each, including forward references and out-of-range wires reading `true`, and
(4) writes the framed output. `SigabaNeoStd` has the compiler and cost lemmas and a gate-list
*generator* (`Prog/GateGen`), but no evaluator of `evalGates` as a tape program and no
loop-over-all-assignments routine with a proven step count; `FromPolyTime` and `Guarded` give
only existence (an unspecified polynomial). Those two routines are the missing pieces.
