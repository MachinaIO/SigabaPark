---
title: A split-witness LWE route for the full CircuitSAT relation and its exponent frontier
refs: [definition:WE_CircuitSAT, note:we-circuitsat-bruteforce-explicit-cost, note:pq-we-route-survey, theorem:AdvancedEncryption.WE.XWE.split_frontier, theorem:AdvancedEncryption.WE.XWE.hybrid_gain_budget]
tags: [witness-encryption, lattice, attribute-based-encryption, cost]
---

## An intermediate construction for every circuit

The 128-input, 4096-gate target admits a middle ground between deciding SAT inside Enc and seeking polynomial-size WE. Use the ABE-to-XWE construction of [ePrint 2017/874, Theorems 3.2 and 3.4 and Corollary 3.3](https://eprint.iacr.org/2017/874.pdf). Its LWE instantiation is conditional on subexponential hardness. The construction uses key-policy ABE directly and has no witness-tree transition keys. Exponential tables are part of the ciphertext. An exponential-time construction can still be compared with the explicit finite baseline under this primitive's cost function.

Split a witness into blocks of lengths a, b, c. For each prefix u issue an ABE functional key for the predicate on v that accepts when some c-bit tail completes (u,v) to an accepting witness. All keys and ciphertexts in one WE encryption use the **same** fresh master setup. For each b-bit v publish one encryption of the message with attribute v. Decryption selects the key and ciphertext indexed by the supplied prefix and middle block. Its tail certifies that this single selected pair is authorized. Thus a per-pair correctness bound suffices for the registered per-witness correctness game. On a false circuit *every* issued key rejects *every* published attribute, including all keys issued under the challenge master key. This is what permits the ordinary collusion-secure ABE game at each hybrid. The verifier in this specialization must implement the registered gate semantics, including default values at forward references.

## What is optimal within this construction?

For the short-functional-key variant the dominant table/circuit exponents, suppressing polynomial factors, are E = max(a+c,b) for encryption work, S = max(a,b) for ciphertext length and D = max(a,b,c) for sequential decryption work. A single-challenge proof switches 2^b entries. The three contributions to D include rebuilding/evaluating the selected predicate with its 2^c tail assignments. Merely indexing the tables on a RAM does not pay for this work.

The theorem split_frontier gives an exact feasibility test. With n witness bits, caps e and d on E and D, and a cap h on b, the five inequalities are n ≤ 2e, n ≤ e+d, n ≤ 3d, n ≤ h+e, and n ≤ h+2d. A construction takes b = min(n,h,e,d), puts min(d,n-b) bits in a, and puts the rest in c. In particular, without a hop cap and with e ≥ ceil(n/2), the least possible d is max(ceil(n/3), n-e) using truncated subtraction. These are optima for the displayed exponent model.

| (a,b,c) | E | S | D | b | 128+2b |
|---|---:|---:|---:|---:|---:|
| (64,64,0) | 64 | 64 | 64 | 64 | 256 |
| (36,56,36) | 72 | 56 | 56 | 56 | 240 |
| (40,48,40) | 80 | 48 | 48 | 48 | 224 |
| (42,43,43) | 85 | 43 | 43 | 43 | 214 |
| (43,42,43) | 86 | 43 | 43 | 42 | 212 |

For example, one extra encryption exponent in the last row halves the number of challenge ciphertexts while retaining the same dominant exponents for size and decryption. The registered baseline is a certified machine cost near 2^188. None of these E entries is a candidate value of that cost.

## Where concrete security must be spent

Write p_j for the fixed adversary's probability of outputting one after the first j entries have switched messages. If each hop of a table of length M has 2^k (p_(j+1)-p_j)^2 ≤ C_j, then hybrid_gain_budget gives 2^k (p_M-p_0)^2 ≤ M times the sum of C_j. This keeps costs of generating all companion ciphertexts, issuing keys and embedding the challenged position visible. When every C_j ≤ r times the original adversary cost, a sufficient bit budget is k ≥ 128+2b+ceil(log2 r) for M=2^b and r≥1. The final table column isolates the term before this cost inflation. This single-challenge accounting is sufficient; it is not an LWE hardness estimate. An ABE-to-LWE proof may itself lose advantage or introduce statistical errors. An existential choice of the distinguished entry also needs its index and the fixed statement accounted for in the concrete machine description.

## Remaining evidence for a submission

The next cryptographic obligation is an explicit public-key, selective-attribute ABE game for the entire set of unauthorized key queries, with a single challenged entry and the ability to generate the other entries under the *same* public parameters. Derive its quantitative guarantee from a member of the registered LWE family. Verify concrete depth/noise, sampling error and key-generation cost for the disjunction of 2^c copies of the actual gate evaluator. Bound construction and sequential traversal of both tables in the project's tape model before comparing N with the baseline. The primitive currently quantifies over its registered Machine adversaries. A claim about quantum distinguishers requires the corresponding post-quantum security of the ABE reduction and LWE assumption. The two accompanying Lean proofs establish the resource and hybrid arithmetic only.
