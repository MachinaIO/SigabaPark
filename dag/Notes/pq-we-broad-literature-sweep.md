---
title: Broad literature sweep for post-quantum WE beyond GGH15 / BGG+ (2018-2026) - candidates ranked by fit to WE_CircuitSAT
refs: [definition:WE_CircuitSAT, note:pq-we-route-survey, note:pq-we-hybrid-count-barrier, note:pq-we-rank-gap-lattice-barriers, note:we-circuitsat-bruteforce-explicit-cost, note:pq-we-escape-routes-verdicts, note:pq-we-non-lattice-algebras]
tags: [witness-encryption, survey, strategy, literature]
---
A scouting pass over 2018-2026 work on witness encryption (WE) and nearby primitives. It
deliberately looks beyond the GGH15 / BGG+ / constrained-PRF routes already explored in the DAG.
The target is `Def_WE_CircuitSAT`: NAND circuits with `2^12` gates and 128-bit witnesses,
`λ = κ = 128`, security measured as `cost / advantage²`, and cost counted as Turing-machine
steps of one `Enc` plus one `Dec`. The baseline to beat is the assumption-free brute-force
submission of about `2^188` steps (`we-circuitsat-bruteforce-explicit-cost`). The constraints are
those of `pq-we-route-survey`: post-quantum, falsifiable and statement-independent assumptions;
no iO / xiO / null-iO, no evasive LWE, no local mixing.

Sources were read from the full text (ePrint through a browser, arXiv through its API) where a
claim below depends on details. Everything else is from the abstract and is marked as such. The
cost figures in Lead 1 are rough estimates by the submitting agent, not taken from any paper.

## Ranked candidates

### 1. Non-trivially exponentially efficient WE (XWE) from plain LWE - fits every constraint today

**Source.** Brakerski, Jain, Komargodski, Passelègue, Wichs, *Non-Trivial Witness Encryption and
Null-iO from Standard Assumptions*, SCN 2018, ePrint 2017/874, Theorem 3.2 and Corollary 3.3.

**Claim.** From any (secret-key suffices) key-policy ABE for all circuits, there is WE for any NP
relation with witness length `m` in which encryption time, ciphertext size and decryption time are
`2^{m/2} · poly`. With the LWE-based ABE of Boneh et al. (BGG+14) or Gorbunov–Vaikuntanathan–Wee
(GVW13), this needs only **sub-exponential plain LWE**. Construction: split `w = w1 ‖ w2`. `Enc`
samples an ABE master key, issues a key for `f_{w1}(·) = φ(w1 ‖ ·)` for every `w1 ∈ {0,1}^{m/2}`,
and encrypts `b` under attribute `w2` for every `w2 ∈ {0,1}^{m/2}`. `Dec` uses the one key/ciphertext
pair indexed by its witness. On a false statement every pair is unauthorized, so selective ABE
security applies to each ciphertext.

**Fit.** Plain or Ring-LWE, falsifiable and statement-independent. No iO and no evasive LWE. The
security proof is a hybrid over the `2^{64}` ciphertexts, so it is an explicit instance of the
"exponentially many hops" escape that `pq-we-hybrid-count-barrier` says is the only one left. It
is also consistent with that barrier, because encryption is not polynomial-time.

**Adaptation to n = 128.**

* `2^{64}` keys and `2^{64}` ciphertexts. The witness-indexed hybrid costs `2^{64}` in advantage,
  which is `2·64` bits of `cost/adv²`. Each hop's reduction runs the encryptor, so the premise must
  be about `128 + 128 + log2(Enc cost / ciphertext size)` bits. Roughly `270`-`320` bits of LWE
  hardness are needed. That is large but allowed.
* **The bottleneck is circuit depth.** BGG+ noise grows by a factor of about `√m`-`m` per NAND
  level, and an arbitrary `2^12`-gate circuit can have depth `4096`. A rough self-consistent
  estimate with Ring-LWE puts `log q` near `2^16`, the ring degree near `2^23` (at the roughly
  300-bit LWE premise), about `2^60` ring operations per gate for public-key evaluation, about
  `2^72` per key and about `2^136` for all keys before Turing-machine overhead. That is plausibly
  below `2^188`, but not by a wide margin. Shallow circuits are far cheaper. These figures must be
  redone carefully before any claim.
* Useful levers: (i) an **unbalanced split**, which moves bits between the key side and the
  ciphertext side to balance their costs; (ii) **partial evaluation**: gates that depend only on
  `w1` are hard-wired in the key, gates that depend only on `w2` can be precomputed in the
  attribute, and only mixed gates are evaluated homomorphically; (iii) any LWE-based ABE whose
  modulus is independent of depth. HLL23 (ePrint 2023/1716) has that, but its full ABE uses
  evasive circular LWE, which is excluded; its 1-key ABE and LFE use only circular security,
  which is allowed but too weak for `2^{64}` keys.
* **Compression below `1/2` is open.** BJKPW Appendix A gets `2^{m/(k+1)}` from `k`-input ABE.
  Known 2-input ABE needs pairings plus GGM or KOALA (Agrawal–Yadav–Yamada, CRYPTO 2022).
  Constant-arity versions use evasive / tensor LWE (Agrawal–Rossi–Yadav–Yamada, ePrint 2023/941).
  Neither fits. A **secret-key 2-input ABE from plain LWE** would cut encryption to about
  `2^{43}` keys/ciphertexts, and is a crisp, self-contained open target.

**Next step.** Formalize ABE-to-XWE as a theorem node with the explicit hybrid loss. Then write a
concrete cost model for a Ring-LWE BGG+ key-policy ABE at depth `≤ 4096` to settle whether it beats
`2^188`, and by how much. This is the only candidate in the sweep that could yield a **non-trivial
submission with a complete proof from allowed assumptions now**.

### 2. Code-based gap reductions: GapMDC (Jin, ePrint 2026/2063) as the combinatorial core of a "linear-test" encoding

**Sources.** Z. Jin, *Witness Encryption for NP from SNARGs and Groups*, ePrint 2026/2063
(Theorems 1.1-1.3, read in full text). Barta–Ishai–Ostrovsky–Wu, CRYPTO 2020 (BIOW20).
Campanelli, ePrint 2026/2399 (abstract). Hair–Sahai, arXiv 2511.04125 / ePrint 2025/2181
(deterministic hardness of GapSVP_p).

**Claim.** A deterministic **Levin** reduction maps SAT instances of size `(log n)^A` to
`⌈log² n⌉`-GapMDC over a prime field `F_p` with `2^n < p < 2^{n+1}` (Theorem 1.3, adapted from
Hair–Sahai). Through BIOW's ciphertext `(g^{Hr + s·t + e}, t, g^{s+m})` with sparse `e`, this gives
extractable WE for polylog-size circuits in the **generic group model** (unconditionally), and WE
for NP when combined with sub-exponentially sound SNARGs.

**Fit.** Not post-quantum: the GGM forbids non-linear tests. Without the group, the encoding
`Hr + s·t + e` in the clear is a sparse-noise decoding problem on the statement's own code, which
is statement-dependent and open to information-set decoding. What transfers is the
**combinatorial gap**: a code (Hamming-weight) gap, an alternative to Hair–Sahai's rank gap,
reached by an explicit reduction with witness maps.

**Adaptation.** This is Direction 1 of `pq-we-route-survey` with "rank" replaced by "Hamming
weight". It meets the same obstacle: a post-quantum encoding that allows only the one linear test
(Barrier 1 of `pq-we-rank-gap-lattice-barriers`). The reduction's blow-up is sub-exponential,
`exp(2^{√log s · (log log s)^{O(1)}})`, and its concrete size for `s ≈ 2^12` gates is unknown. It
should be computed before any use. Rank 2 because it gives a second, independent gap source.

### 3. WE ⇔ laconic SHVZK arguments ⇔ predictable arguments - a reformulation target

**Sources.** Liu–Mazor–Pass, *On Witness Encryption and Laconic Zero-Knowledge Arguments*, ePrint
2024/1932 (Theorem 1.1, Corollary 5.2, read in full text). Faonio–Nielsen–Venturi, PKC 2017.
Bitansky–Choudhuri, TCC 2020 (deterministic-prover ZK). Kiyoshima 2024 (strong WI / resettable
statistical ZK imply predictable arguments).

**Claim.** For every NP language `L`, WE for `L` exists iff an efficient-prover **laconic**
(`O(log n)`-bit prover messages) special-honest-verifier ZK argument for `L` exists. Statistical
WE corresponds to laconic SHVZK *proofs*. A completeness-soundness gap of `1/poly` already
suffices (Corollary 5.2): weak WE is amplified internally.

**Fit.** No assumption of its own, so it is a target, not a construction. It suggests searching
the post-quantum proof-system literature (LWE/LPN commitments, Σ-protocols, MPC-in-the-head) for an
argument for Circuit-SAT that is **simultaneously laconic and special-HVZK**. The `1/poly`
tolerance is attractive concretely, since a constant-gap object would do. It inherits the SZK
barrier of `pq-we-hybrid-count-barrier`: a laconic SHVZK argument from statement-independent
assumptions with a polynomial-hop soundness proof would put `L` in SZK. A fine-grained version
(exponential-time verifier or simulator, mirroring Lead 1) is the natural variant to look for.

### 4. Propositional-proof SNARGs from LWE - a refutation-indexed alternative to witness-indexed hybrids

**Sources.** Jin–Kalai–Lombardi–Vaikuntanathan, *SNARGs under LWE via Propositional Proofs*, STOC
2024, ePrint 2024/956. Jin–Lu–Peng, *SNARKs from LWE via Non-black-box Reductions*, STOC 2026,
ePrint 2026/2805 ("Cryptographic Extended Frege"). Jin–Kalai–Lombardi–Mathialagan, ePrint 2024/2015.
An ECCC 2026 report (TR26-098) extends this to all of NP under derandomization plus LWE/SXDH.
Abstract-level reading only.

**Claim.** From LWE, SNARGs for NP languages whose **non-membership has short Extended Frege
proofs**. The soundness reduction follows the refutation line by line through an
"encrypt-hash-and-BARG" template.

**Fit / adaptation.** SNARGs do not give WE. The transferable idea is that security reductions can
be indexed by the steps of a **refutation of the false statement** instead of by candidate
witnesses. Every unsatisfiable 128-input circuit has a tree-like resolution refutation of size at
most about `2^{129}` times its size. A WE whose hybrids walk a refutation would therefore have the
same `2^{128}`-hop budget as `pq-we-hybrid-count-barrier`, and would be far cheaper on instances
with short refutations. This is speculative: no WE analogue of these SNARGs is known, and
worst-case instances have exponentially long refutations in weak systems. Recorded because it is
the only standard-model, LWE-only line in which **statement-specific proofs of falsity** drive
the security argument.

### 5. Positional WE and other "WE + LWE" upgrades - tools for after a base scheme exists

**Sources.** Nassar–Waters–Wu, *Obfuscating Non-Evasive Programs: Making Witness Encryption
Positional*, ePrint 2026/1932 (Theorem 1.1, full text). Devadas–Jain–Waters–Wu, ePrint 2025/944
(succinct WE for batch languages). Nassar–Waters–Wu, ePrint 2026/2436 (threshold BARGs from WE +
LWE).

**Claim.** WE plus LWE gives cutoff-iO and hence **indexed positional WE**, which previously
needed iO. Positional WE is exactly the witness-indexed hybrid structure that
`pq-we-hybrid-count-barrier` calls for.

**Fit.** These assume WE, so they are not a base. They do show that once any WE exists (for
example the XWE of Lead 1), the positional structure and several succinctness upgrades come at the
price of LWE alone. Whether the cutoff-iO compiler preserves the `2^{m/2}` efficiency of XWE is a
concrete question.

### 6. Fixed-gap rank encodings with exponential decryption search (Praxis) - an idea, not a fit

**Source.** Tse–Vanjani–Vesely, *Praxis: Practical Witness Encryption for NP*, ePrint 2026/2971 /
arXiv 2611.28552 (abstract). Extractable in the bilinear GGM plus ROM under Module-SIS. It keeps
Hair–Sahai's gap fixed and decrypts by a search of `O(2^{λ/4} N^{1/4})` operations.

**Fit.** Pairings, so not post-quantum. The transferable lesson is that the cost model allows
**exponential but sub-`2^{188}` decryption**. A fixed gap plus brute-force search at decryption is
legitimate here and relaxes the parameters of any rank- or weight-gap scheme (Lead 2).

## Checked and excluded

| Item | Why excluded |
| --- | --- |
| Hair–Sahai arXiv 2609.18275; Jutla ePrint 2026/2995; Campanelli 2026/2399; Jin 2026/2063; BIOW20; GHK+25 linearly verifiable SNARK WE (ePrint 2025/1364, read in full: GGM / pairing gadgets for special relations); Praxis | generic or bilinear groups: not post-quantum. Useful only as templates (Leads 2 and 6) |
| VWW22 (2022/1140), Tsabary 2022, HLL23 full ABE (2023/1716), pseudorandom obfuscation (2024/1742: evasive-LWE heuristic), multi-input ABE (2023/941; AYY22 with KOALA), Chen–Vaikuntanathan 2026/2346 (KOALA + iO), succinct obfuscation via PV proofs (2026/2009: iO), proof-complexity generators (2026/2813: iO-based applications) | evasive LWE, knowledge assumptions, or iO |
| Affine determinant programs: BIJ+20; Soukhanov et al. 2026/175 | heuristic, and broken (ePrint 2026/1594, 2026/1583) |
| Chen–Li ePrint 2023/1894 (WE for a promise problem in NP \ coNP/poly from lattice/code PKE); lattice SPHFs | languages not NP-hard; no route to Circuit-SAT |
| Li–Ni–Zan ePrint 2023/1260 (claims WE for NP from OWF) | not credible as stated: it would contradict the SZK barrier of `pq-we-hybrid-count-barrier` and long-standing open problems; not used |
| Choi–Vaudenay, ICISC 2020 (subset-sum WE) | RSA-type hidden-order groups plus knowledge-of-exponent; no NP-hardness reduction; not post-quantum |
| Witness encryption for QMA / quantum null-iO (Bartusek–Malavolta 2021); Barhoush–Morimae–Movassagh arXiv 2608.25195 | quantum ciphertexts or classical WE for QMA; the latter is a black-box barrier for WE for QMA from falsifiable assumptions, not for NP |
| Isogeny / group-action, code- and tensor-isomorphism, MQ, hash-based (ROM / QROM) WE | no construction found in the sweep; the algebraic verdicts of `pq-we-non-lattice-algebras` stand |

## Adjacent fields: what transfers

* **Algebraic proof complexity.** In linear-test schemes (rank gap, GapMDC) an attack corresponds
  to a "pseudo-witness" for a linear relaxation of the statement. Polynomial-calculus and SOS
  lower bounds (Ben-Sasson–Impagliazzo 1999; Alekhnovich–Razborov 2001) show that natural CNF
  encodings of random unsatisfiable instances *have* such pseudo-solutions up to degree `Ω(n)`.
  So any degree-`d`-test encoding needs a gap-creating reduction (PCP-based, as in Hair–Sahai and
  Jin) rather than the circuit's own constraints.
* **Fine-grained cryptography.** Apart from XWE, no fine-grained WE was found. The cost model
  (`2^{188}` brute-force baseline, 128-bit `cost/adv²`) leaves room for exponential `Enc` *and*
  `Dec`, which most of the literature ignores. Leads 1 and 6 are the two ways this room has been
  used.

## Summary

The only allowed-assumption construction with a proof that is non-trivial at `n = 128` is
**BJKPW's ABE-split XWE (Lead 1)**: plain or Ring-LWE, a `2^{64}`-hop proof, cost about
`2^{64} × (ABE key + ciphertext)`. The decisive open quantity is its concrete cost at circuit
depth up to `4096`. Leads 2-4 are research directions: a code-weight gap, laconic SHVZK, and
refutation-indexed hybrids. Lead 5 gives upgrades once a base scheme exists.
