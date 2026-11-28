---
title: Exact cost of the dense correction encoder for the separating terminal
refs: [definition:SeparatingTerminalMachine, definition:WE_SeparatingTerminal]
tags: [witness-encryption, finite-control, cost]
---

The machine SeparatingTerminalMachine.encCorrection reads the message and then, for each of 63 terms, two private share coins and 12672 private pad bits. Every term and source slot has one fixed position in the private input. At an eligible position the output is the role share XOR the pad. At every other position it is zero. The theorem encCorrection_run proves this for every message, all 126 term coins and every dense array of pads. With independent uniform coins and pads, forgetting the ineligible dummy inputs recovers the earlier independent-pad experiment.

The transition table contains the input-position schedule. Its field arithmetic is executable on pairs modulo three with the second coordinate representing a square root of minus one. The theorem allow_iff proves that the table uses the previous separation predicate. The compiled deterministic transducer uses no work tape. Its logical states consist of an input position and three bit registers. The standard transducer compiler introduces a factor of six for a pending symbol and finalization. There are 38326272 compiled states, 798463 input bits, and 798336 output bits. The clock is 1596929. The canonical transition table costs 6898728960 description bits. Their sum is exactly 6900325889, as certified by encCorrection_cost. The charge includes the whole eligibility table in finite control. Encoding the eligibility predicate does not require additional input tags.

This cost covers generation of the public correction stream from a private operand word. A complete encryption machine must also generate the private randomness, prepare or read that word, and protect the designated pad subsets with a supplier. Decryption must provide the authorized openings. Those costs and the all-circuit false-statement reduction require separate certificates.
