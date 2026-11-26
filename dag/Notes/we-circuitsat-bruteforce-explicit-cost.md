---
title: Brute-force WE for NAND-circuit SAT with an explicit cost (about 2^188)
refs: [definition:WE_CircuitSAT, definition:WE_CircuitSAT_Impl_BruteForceExplicit, theorem:AdvancedEncryption.WE.CircuitSAT.BruteForceExplicit.submissionProp, note:we-circuitsat-bruteforce-baseline]
tags: [witness-encryption, baseline, submission, machines]
---
`AdvancedEncryption.WE.CircuitSAT.BruteForceExplicit.u` is an assumption-free submission for
`WE_CircuitSAT` (no premises) whose claimed cost is an **explicit number**:

    N = 381461057563519853491131165268104433667487467501207004940  (about 2^187.96)

with a complete proof of `SubmissionProp u`. It replaces the existence-level baseline
(`WE_CircuitSAT_Impl_BruteForce`, whose `N` is not explicit).

**Algorithms.** Both are tape programs (`SigabaNeo.Tape.Prog`, compiled by `XProg.toMachineT`,
coin-free hence deterministic).

* `Enc` (`BF.encProg`, 40 tapes, 9838 compiled states) builds templates by doubling loops, then
  runs 8 nested loops of `2^16` rounds over a 128-bit counter `X` (incremented with `carry addBit`).
  Each round evaluates the circuit on the assignment `x_i = X[127-i]` by streaming the *whole input
  word* `encodeTuple [pw, encGates φ, [β]]` bit by bit through a three-level frame decoder
  (`step1`/`step2`/`step3` in the proof). Wires live in a 4225-bit register (wire `i` at position
  `4224 - i`); a unary index is a one-hot marker shifted once per digit; a lookup
  (`∃ pos, A ∧ ¬G`, read off the first digit), a gate write and a marker shift are each one `carry`
  primitive, so forward and out-of-range wires read `true` exactly as `evalGates`. The OR of the
  outputs and `β` give the output frame `[true, β && sat φ, false] = encodeTuple [[β && sat φ]]`.
* `Dec` (`BF.decProg`) shifts its input through a 3-bit register: the last three bits are the
  frame of the ciphertext `[b]`.

**Cost.** The clocks are `XProg.totalTimeT` with per-tape bounds; `timeBoundT` is certified by
`NB.check` (`decide +kernel`): Enc ≤ 381461057563519853491131165267976641333226266624117730554
steps from inputs of at most 207643659 bits, Dec ≤ 258695979056124760 from 207643916 bits;
`descLen` adds `6·9842·3^40·178 ≈ 2^86.7` and `6·368·27·25`.

**Where the cost goes, and how to lower it.** Every primitive sweeps all tapes, and the input
stream is about `2^27.6` bits, so one evaluation costs about `2^27.6` rounds of about 13 sweeps of
`2^28.6` cells, i.e. `2^60`; times `2^128` assignments gives `2^188`. The intrinsic count is
`2^128 · 2^12` gates. Routes to about `2^165`, all NoGrow (so still certifiable by `NB.check`):
pre-parse the circuit once into a compact word of `2^12 · 26` bits (binary indices, via a 13-bit
counter), clear the input, and look wires up by comparing a replicated index word against a
position-code register (slots of 14 bits, a handful of `carry` primitives per bit of the index).
The per-evaluation cost then drops to about `2^37`.

**Reusable pieces in the proof** (candidates for `SigabaNeoStd/Machines`): the stream automaton and
its fold lemma over `encGates`; the one-hot / wire-register `carry` lemmas (`hd_lookup`,
`write_encW`, `shift_hot`); `run_update_of_bfAvoids` (a program that never mentions a tape commutes
with its updates); counting through all 128-bit words with `carry addBit` (`orIter_all`).
