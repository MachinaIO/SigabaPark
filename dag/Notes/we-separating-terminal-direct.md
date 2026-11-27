---
title: Dense correction encoder below the two-to-the-thirtieth cost threshold
refs: [definition:SeparatingTerminalDirect, definition:SeparatingTerminalMachine, definition:WE_SeparatingTerminal]
tags: [witness-encryption, finite-control, cost]
---

Every input symbol of the correction encoder emits zero or one bit; the end of input emits none. The direct compiler exploits these properties by advancing one cell on every input bit and halting when it reaches the right end marker. Its states are an input position and three bit registers. The main output theorem Direct.dense_run proves equality to the preceding machine on every complete private operand word. It therefore gives the same field-derived corrections, in the same dense order and with the same zero padding.

The input has 798463 bits. Direct.dense takes exactly 798464 steps including its end-marker step. With no work tapes and 6387712 states, its transition table costs 1034809344 bits. Direct.dense_cost proves a total of 1035607808, below both 2^30 and 2^32. The finite control fixes the eligibility decision at each position and pays the full description cost. Computing eligibility online or deleting the dummy slots is unnecessary for this local bound.

The private word contains the message, the two fresh coins for each term, and the dense pad values. Costs for preparing this word, generating or protecting source pads, and providing authorized openings still belong to the surrounding construction. If a runtime field evaluator replaces the compiled schedule, its arithmetic, tape movements, and state table require a new cost proof.

A full-size replay folded all 798463 opcodes in fixedPlan using the same update and emit functions. For all-zero pads, first term coins uniformly fixed to false, and second term coins uniformly fixed to true, both messages produced exactly 798336 correction bits. Their one-bit counts were 266112 for message zero and 236544 for message one. The difference of 29568 is exactly the number of eligible J slots. These deterministic test vectors exercise serialization and arithmetic. The hiding proof uses fresh uniform coins and pads.
