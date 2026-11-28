---
title: Computationally predictable-on-NO labels from a fixed LWE bank and witness-indexed share buckets
refs: [definition:WE_CircuitSAT_Capped, definition:BucketLabel, theorem:AdvancedEncryption.WE.BucketLabel.idealCoupling, theorem:AdvancedEncryption.WE.BucketLabel.authorized, theorem:AdvancedEncryption.WE.BucketLabel.rowSmallBall, theorem:AdvancedEncryption.WE.BucketLabel.predictorGap, theorem:AdvancedEncryption.WE.BucketLabel.publicMasks, theorem:AdvancedEncryption.WE.BucketLabel.hybridSquared]
tags: [witness-encryption, lwe, secret-sharing, prediction]
---

### Which predictor can a witness run?

Goldberg and Kabanets, *Witness Encryption and NP-Hardness of Learning*, CCC 2025, Lemma 64, publish seed z in an example and pad the concatenation of the n masked Δ-bit share blocks to 2nΔ bits. The label is b. Each mask bit is an encoded truth-table evaluation of f_i on one prescribed restriction of z. Their YES circuit uses the small authorized set T, at most θΔ evaluations and fewer than γ(Δ)^−4 total queries to f_T; critically it hardwires f_T, T and the statement. Its bound is O(θλ) gates. Lemma 65 obtains the simultaneous incompressibility of random advice with probability at least 1−2^−n. Theorem 66 is a randomized many-one reduction using this advice, with NO prediction bounded only for circuits of the stated size s₂=s₁g/log³n. It does not give those tables to the original SAT witness. Theorem 67 obtains an honest half-Levin reduction in a distributional **oracle** model, with oracle WE already available; its predictor calls oracle Dec. These are distinct results. [Official article, Sections 2 and 3](https://doi.org/10.4230/LIPIcs.CCC.2025.34)

If all f_i (nλ advice bits) and their evaluation algorithms are public, an authorized full variable set uses nΔ encoded evaluations, nΔ bit flips, and one call to Rec(φ,[n],·). It recovers b on every sample, including negative gap-MMSA instances with no *small* authorized set but a satisfying all-variables assignment. For example, an AND of sufficiently many distinct variables has this property when its minimum exceeds θg. Success is 1 and gain over random guessing is 1/2. This is an algorithm on the changed advice interface. The paper's bound applies to its specified predictor-size model and is not contradicted. For this simple changed interface, a finite challenger can use XOR sharing for AND; after unmasking, adding all shares returns b.

### Fixed-source construction for a circuit-recognizable restricted relation

Split the original 128 witness bits into role strings u_i. Each public local subcircuit F_i reads only its role and emits a tag of the same prescribed width. Require equality of the tags for an AND-of-roles gate, or satisfaction of an authorized role set in a single tag bucket for the shared predicate below. An equality-of-tags circuit can be implemented as local NAND computations followed by bit equality and conjunction; only circuit families whose statement is publicly verified to have this semantics are covered. The witness directly supplies every lookup address. No other examples, hidden lookup tables, external oracle or per-witness advice are required.

Use one fixed, statement-independent registered decision LWE tuple with uniform matrix A modulo q and b=As+e, where s and e are independent entrywise CBD(1). Let U be a statement-independent upper bound on distinct tags, d the number of random field elements per tag and T the training count; take m=T+dU rows even if fewer tags appear. Sort the public list of tags and use their deterministic distinct-tag rank. Unused same-sized challenge rows are discarded or their A entries may be public. Expose T **fresh, disjoint** training pairs (A,b) under the same secret; expose the remaining A features. For each tag t take r_t to be its d allocated b entries. Publish in each occurrence of role i the residue Λ_i r_t + γ_i Δβ, where Δ is a public message scale. Duplicated occurrences under a role and tag use the same value. Tag ranks can be recomputed from the statement, or sent and charged. The genuine public examples are obtained by sampling β fairly and applying this issuer. For WE encrypt the supplied β directly.

A YES witness supplies a tag and reconstruction weights c_i with Σ c_i Λ_i=0 and Σ c_i γ_i=1. Its selected shares sum exactly to Δβ for every coin sequence, including LWE errors. For a NO, assume that for every bucket's *actually represented* role set there is h_t with Λ_i h_t=γ_i Δ there. In the uniform challenge all r_t are independent uniform even conditional on training and A. Translation by h_t is a bijection absorbing the message change simultaneously in the whole transcript. The honest issuer and reduction do not need any h_t. Repetitions within a bucket cause no issue. This is an affine coupling only on the ideal side of a fixed-distribution reduction.

For k-role equality take d=k−1, the first k−1 roles' shares r₁,...,r_{k−1}, and the last role Δβ−Σr_i. If the last role is absent use zero translation. Otherwise an earlier role is missing; translating only that missing coordinate by −Δ realizes the last-role shift, even if every OTHER role is represented. Across different buckets every role can be visible on the NO. This avoids making public a global family of share masks for the all-variables set. All public computations, including the splitting layout, are classically computable; this is not general predicate garbling or free-XOR LPN garbling. One does not publish both correlated wire labels under a global offset. Individual role descriptors can be nonlinear within their own inputs.

### A negative instance can reveal the bit to unlimited computation

At q=16 choose k=4, Δ=8. A secret-searching predictor enumerates at most 3^n possible ternary secrets and keeps those whose T unshifted residuals all belong to {−1,0,1}. Fix the true secret and a wrong candidate. Some coordinate difference is ±1 or ±2. After fixing the other uniform row coordinates, at most six of the sixteen possible remaining coordinates put the difference in {−2,...,2}. Independence between rows and a union bound show the true secret is unique except with probability at most 3^n(6/16)^T. At T=2n this is (27/64)^n. With the recovered secret the shifted last-role share has phase uncertainty at most three, so its zero and eight cases have disjoint supports. One real last-role occurrence suffices even on an unsatisfiable NO. For k=16,q=64,Δ=32 the same six-residue argument has probability ≤6/64 per row. The fifteen errors sum to a value between −15 and +15, and the two phase intervals again do not intersect. Hence statistical equality is genuinely absent in the **real** laws: equal-prior prediction succeeds at least 1−3^n(6/q)^T, despite the computational reduction. No search oracle is used for YES correctness.

### Fixed challenge, examples and finite accounting

Given any bit predictor with success 1/2+ε on the real NO examples, a reduction samples a fair β, embeds its fixed (A,b) challenge, and tests equality with the predicted bit. Its ideal success is exactly one half. Thus the single challenge has absolute acceptance gap ε. A two-message distinguisher with gap η gives ε=η/2 after an output-sign choice, so its fixed-source **squared** gain is η²/4. For J independent banks, successive replacements give η² bounded via Cauchy–Schwarz by 2J times the sum of the 2J underlying squared gaps. If every embedded test costs at most K times the original adversary, sufficient single-source strength for 128 concrete bits is H≥128+ceil(log₂(4J²K)). K includes public circuit and training generation, sorted-tag assembly, conversion from the exact registered challenge encoding and finite control. A reduction that accesses the examples classically remains valid as an oracle algorithm for a quantum predictor with classical inputs and outputs, conditional on the same fixed source against such algorithms; the registry's Machine statement itself is classical.

Independent labeled training examples with public β can be generated from fresh keys by the reducer; under a persistent secret they require disjoint bank rows per example and must all count toward m. Publishing a known-label example with the same role, tag and masks later used for a fresh test trivially reveals the test shift by subtraction. Unshifted training samples here are raw LWE samples on separate rows. The single test observes an entire share table, including all other examples in the table. No assumption about an SAT-conditioned noisy-label source is made.

With 16 roles of eight witness bits and U=4096, there are 4096 role occurrences and 61440 role-mask rows, plus T=2n training rows. At q=64 and n=1024 the full matrix, training b entries and occurrence shares take 390107136 raw bits; uniform matrix and exact CBD coins take 390199296 fair bits. At n=2048 the corresponding totals are 805355520 and 805441536. The pinned registry returns H=380 and H=762 respectively at precisely these full counts (q=64, secret and error CBD(1)). The tag directory and framing are additional. With 4 roles of 32 bits and q=16 the loose joint count 2n+12·2^32 deduces only H=56 at n=1024 from the pinned estimator; a large number of samples cannot be silently charged as a small challenge. Fixed-size buckets and independent shorter banks can be compared using the squared-hybrid penalty above. Honest dense generation uses mn modular multiply-adds (the ternary secret permits conditional add/subtract), plus tabulation of the 4096 local outputs in the sixteen-role example, sharing, sorting and lookup. A direct public sort can also decide k-way intersection. This restriction and the output-bit counts do not give an end-to-end registered machine or solve arbitrary NAND-SAT.

For a wider two-list promise, choose independently 300 of 128 binary descriptor coordinates with replacement per trial and tag by those selected bits. A valid witness at distance at most one hits with probability (127/128)^300>0.09. In 1024 independent trials its miss probability is below 2^−128. On any promised NO with every cross-pair distance ≥64, the probability of even one false intersection among two 2^64-entry lists in all trials is at most 2^−162. Honest decoding can ignore trials whose witnessed tags differ. Ideal NO prediction deviates by at most half the bad-hash probability; all fresh test rows and construction costs grow with the trials. Without a distance-gap promise, exact distance ≤1 is handled by inserting all one-bit neighbors and the unchanged descriptor on one side, then using equality and witness-selected neighbor indexing. This has a 129-fold occurrence overhead on that side.

Remaining work is a succinct witness-preserving issuer for arbitrary shared-input circuits with jointly simulable conditioned shares and a native budgeted reduction. No new assumption or registry entry is proposed.

### Reproducible finite verification

```python
from itertools import product
from collections import Counter
from fractions import Fraction
for tag in range(15):
    ids=[i for i in range(4) if tag>>i&1]
    def transcript(r,b):
        out=(*r,(8*b-sum(r))%16)
        return tuple(out[i] for i in ids)
    assert Counter(transcript(r,0) for r in product(range(16),repeat=3))==Counter(transcript(r,1) for r in product(range(16),repeat=3))
for r in product(range(16),repeat=3):
    for b in (0,1): assert (sum(r)+(8*b-sum(r))%16)%16==8*b
for q in (16,64):
    worst=max(sum((c+d*x)%q in {q-2,q-1,0,1,2} for x in range(q)) for c in range(q) for d in (-2,-1,1,2))
    assert worst==6
a=Fraction(127,128)**300
assert a>Fraction(9,100)
assert Fraction(91,100)**1024<2**-128
assert 1024*(2**128)*Fraction(1,2)**300==Fraction(1,2**162)
assert (3*Fraction(6,16)**2)**1024 < Fraction(1,2**1024)
for n in [1024,2048]:
    m=61440+2*n
    print(n,m,6*n*m+6*(2*n+4096),6*n*m+2*n+2*m)
print('15 partial role sets, 4096 ideal pads, both shifts; exact LSH and training bounds')
```
