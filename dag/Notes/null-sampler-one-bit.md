---
title: One private input bit in published LWE sampler encodings for a null NAND circuit
refs: [definition:WE_CircuitSAT_Capped, definition:NullSamplerCosts, theorem:AdvancedEncryption.WE.NullSampler.sharedCRS, theorem:AdvancedEncryption.WE.NullSampler.groupedCost, theorem:AdvancedEncryption.WE.NullSampler.fullHeader, theorem:AdvancedEncryption.WE.NullSampler.sparseQueries, theorem:AdvancedEncryption.WE.NullSampler.observableCompression, theorem:AdvancedEncryption.WE.NullSampler.coordinateCode]
tags: [witness-encryption, succinct-randomized-encoding, oblivious-lwe, finite-cost]
---

Fix the registered public 128-input NAND circuit C. Make the bit b the only private input of the function f_C(b)[w]=b AND C(w). The function and gate layout are identical in both worlds; changing the single private data bit preserves length. Equivalently, when representing two circuits as input to a universal evaluator, use the same padded gate skeleton with a final AND and a constant-zero or constant-one selector. Only the first formulation achieves private-input length one. For every witness w of a true instance the specified coordinate equals b. For every false instance the complete outputs coincide. Thus the published equal-output security experiments apply directly at their declared interfaces, with the public function fixed by C and neither its gate count nor the sampler challenge changing with b. This removes any need to use a final general-purpose iO theorem for this functional implication. The underlying sampler assumptions remain outside the registered WE premises, and the goal disallows invoking iO or known iO-implying primitives as a solution.

### What the assumptions expose

Wee–Wichs, revised March 4, 2021: the functional encoding of Sect. 3 uses one opening per specified function/index pair, and its simulator receives those functions and their outputs. Construction 7.1 requires ordinary LWE and an oblivious sampler with a simulation property. Their concrete Construction 6.3 builds its public hints by homomorphic PRF evaluation. Conjecture 6.4 compares two fixed distributions containing ordinary samples, a commitment to the PRF key and flag, and correlated openings that include an evaluation correction and the conditional challenge secret. With all implementations, dimensions and laws pinned, that game mentions no target NAND circuit. HPLS is an additional hypothesis. Hopkins–Jain–Lin give an explicit counterexample for the implementation flexibility in the conjecture, and distinguish this from breaking every specified implementation or the generic conditional functional-encoding theorem. A particular sampler, PRF circuit, sampling circuit, homomorphic evaluation order and noise laws would have to be fixed before assigning a concrete security strength. [Wee–Wichs, Sects. 3, 6–8](https://eprint.iacr.org/2020/1042) · [Hopkins–Jain–Lin, Sect. 4](https://eprint.iacr.org/2021/889)

Devadas–Quach–Vaikuntanathan–Wee–Wichs, revised October 18, 2021: Definition 3.1 requires LWE relative to the generated A* even with setup and generation coins, and a flooding implication quantified over auxiliary distributions satisfying an indistinguishability precondition. This implication is different from a pair of fixed decision distributions. Definition 3.2 fixes the weak flooding experiment; Theorem 3.3 supplies an amplification compiler with additional data and hybrids. Section 4.3 Conjecture 2 specifies the two standalone subspace-flooding distributions. They include projection matrices, seed, A*, a noisy sample with random secret, a gadget-shifted encryption of the flag, and a correlated error term. Its input excludes the concrete NAND circuit, but it is an extra distributional conjecture. In Section 5 the proof gives the commitment as auxiliary information and chooses its homomorphic output error as the bounded perturbation. The equality f_C(0)=f_C(1) holds on a false circuit and makes the ideal sample transformation independent of the input bit. Public coins allowing one to compute S* cannot simply be substituted for the strong game's projection-and-seed postcondition; the two sides of the implication expose different information. Corollaries 5.2/5.3 and the XiO lifting theorem use subexponential hypotheses. They do not give finite constants or a quantum-security reduction at the parameters here. This note proposes no new assumption or registry extension. [Devadas et al., Definitions 2.5, 3.1–3.2 and Sections 4–5](https://eprint.iacr.org/2021/1226)

### Paying the actual WW bank, even when the CRS is shared

Section 8.4 divides the addresses into Q blocks of m parallel outputs. Dec normally forms its m-bit block and returns a single bit. The CRS of Construction 6.3 contains Q uniform m-entry columns. Thus Qm field elements are paid when it is sent with a single direct batch. Section 8.3 can reuse one CRS across multiple independently encoded outer prefix restrictions. For G independent commitments using the same CRS, even with only one private input bit, one secret coordinate and L=ceil(log2 q), the three unavoidable fixed-width fields have sizes at least

    X=Q m L,    Y=G m² L²,    Z=G Q L.

These are the single shared setup, gadget commitments and all indexed openings, respectively. A full cover has GQm≥2^128. Reusing honest CRS for independently randomized commitments admits a G-step selective hybrid because the reduction can generate the other commitments under the challenge CRS; a bound ε for one indexed collection becomes Gε. The published construction uses fresh commitments. Reopening different functions at the same index under one commitment is not a consequence of this argument.

The identity X Y Z²=(GQm)³ L⁵ implies X+Y+Z>2^100 whenever L≥128, which follows already from the reported flooded-noise scale at security parameter 128 with positive bounds. This identity covers the shared-CRS plain-wrapper accounting as well as the direct instantiation and does not charge opening computation or CRS-generation time. For power-of-two partitions and L=128, exhausting all 8,385 exponent triples gives a minimum of 80·2^100 bits at (log G,log Q,log m)=(30,68,30). Treating the CRS as a free oracle, replacing it by a public seed requiring a new simulation argument, or changing the commitment and opening formats changes the model. [WW, Constructions 4.2, 6.3, 7.1 and Theorems 8.3–8.4](https://eprint.iacr.org/2020/1042)

### Paying the actual DQ bank, even with free setup and selective decoding

Write N=MK for the number of table coordinates, W for the column rank used by the sampler after eliminating dependent columns, and L for the residue width. In Section 5 even with private input length one, the transmitted commitment has M²L² bits and the opening V has WKL bits. At N=2^128 and L≥131, every power-of-two shape M=2^r already exceeds 2^100 bits on these two fields alone when W≥93. The integer threshold from these two fields is sharp: W=92, r=42 gives 1,264,420,350,438,219,112,341,888,303,104 bits; other fields are uncharged. The L bound uses q≥8·2^λ αB with λ=128 and αB≥1. These estimates do not require materializing the full decrypted table.

More strongly, apply the actual Section 4.3 balanced tensor parameters N=m^(2d), d≥4, M=m^(d−1/2), K=m^(d+1/2), W≥w m^(d−1), w≥1. For exact integral powers at N=2^128, m≤2^16, so M²=N/m≥2^112 and WK≥N/sqrt(m)≥2^120. Each field alone is too large before charging field widths. For a nonuniform cover by candidate instances of sizes N_j≤2^128 in the exact square-m template, each pays at least N_j/256 opening entries. Summing over any cover still costs at least 2^120 entries, even if blocks overlap or share setup. The groupedCost proof uses u=sqrt(m) and d=4+k, and makes no assumption about polynomial notation, concrete LWE hardness or a hidden constant. Rounding parameters, a different candidate family or a different way of representing V requires separate analysis.

A single coefficient of the Section 4.1 expansion is the contraction of one row of P, the tensor product of the d public B factors, and one column of P'. It can be computed without storing all MK coefficients: multiply that column by one small B factor per tensor mode and finish with the row dot product. For m-by-k factors the operation uses Σ_{h=1}^d m^h k^(d−h+1) scalar multiplications plus m^d for the dot. The explicit target column of P' alone has k^d entries; in Section 4.3 k≥m³, so this is at least N^(3/2)=2^192 entries. A literal dense contraction at even one coordinate does not fit. This cost refers to the concrete dense traversal, not an unconditional lower bound on all evaluators. The final rounding can indeed use just the specified entry of Cf, this contraction and the corresponding dot of an A* row with a V column. Exposing compressed factors of S* or the private Evalopen coins instead changes the transcript and needs a proof. [Devadas et al., Section 4.1, parameter setting and Remark 4.1 in Section 4.3, Section 5](https://eprint.iacr.org/2021/1226)

### Which compression steps preserve the game?

An efficient deterministic projection of an already secure *joint* transcript preserves its distinguishing bound; a seed revealing hidden generation coins need not do so. If every needed opening column equals a publicly prescribed linear combination of retained columns in both worlds, one can substitute them in decoding. Construction time must also be charged: obtaining those columns by first computing the entire dense opening defeats the finite-clock objective. More generally, an exact compressed clear value z_C(b) with equal values on every false instance and opposite decoded bits on every satisfying witness has z_C(0)≠z_C(1) exactly on satisfiable instances. If a compiler makes both values cheaply available, comparing them supplies a public SAT test at the same compilation cost. This reasoning uses the available *whole clear compressed value*, not just short encrypted samples or a short program representing a function of the address. The observableCompression lemma formalizes this distinction.

Two further limits quantify possible alternatives without denying source-level optimizations.

* An adaptive oracle-only preprocessing tree observes truth bits C(i) and may output arbitrary data to the rest of the algorithm. Run it on the zero truth table. Changing only bit v cannot change its output unless the zero run visits v. The sparseQueries theorem sums this coupling for two distinct bit-dependent adaptive algorithms and arbitrary per-target tests. For n=2^128 addresses, if testing the unique witness on point v separates payloads with acceptance gap at least 1−2ε while the same test on zero has gap at most δ, the two zero-runs together must inspect at least n(1−2ε−δ) distinct positions in expectation. Thus ε=2^−128 and δ≤1/2 force one of the two expected costs above 2^125. A tester can fix the positive instance and its unique witness when looking at the zero transcript provided the compiler has only oracle access and preserves the public interface. Explicit-circuit source analysis or instance-dependent helper data outside that model is not covered.
* A reusable codec supporting coordinate probes into an arbitrary uniform n-bit column, with k-bit code, satisfies 2^n≤2^k plus the total number of bit errors across all column/index pairs. On words decoded exactly the encoder is injective; every other word contributes at least one error. The coordinateCode proof permits averaging over public and private coins by fixing them first. Given a per-coordinate error at most ε under a uniform n-bit column, this yields 1≤2^(k−n)+nε. For n=2^100+1 and ε=2^−128, even k=2^100 violates this inequality. In a tensor contraction serving every one-hot product query, such a query just returns a specified column entry. This rules out an error-tolerant, independent, universal one-hot-query codec for uniform data; it does not assert that the actual noise column is uniform binary or that random honest factors realize every probe with appreciable probability.

Open tasks are a source-aware map from arbitrary 4,096-gate circuits that avoids paying for every witness, an authorized statement-independent registered reduction for the full reduced transcript, and concrete costs for any new factor generation and verification. Neither the point-oracle result nor the measured shape bounds rule out a different one-bit release construction.

### Numerical replay

```python
from itertools import product
n=2**128
cap=2**100
parts=[(2**(q+m)*128+2**(g+2*m)*128**2+2**(g+q)*128,g,q,m)
       for g in range(129) for q in range(129-g) for m in [128-g-q]]
assert len(parts)==8385 and min(parts)==(80*cap,30,68,30)
for w in (92,93):
 v,r=min((131**2*2**(2*r)+131*w*2**(128-r),r) for r in range(129))
 print(w,r,v)
 assert (v>cap)==(w==93)
for d in (4,8,16,32):
 u=2**(128//(4*d));m=u*u
 N=m**(2*d);M=u**(2*d-1);K=u**(2*d+1);W=u**(2*d-2)
 assert N==n and M*K==N and M*M>=2**112 and W*K>=2**120
 print(d,M.bit_length()-1,K.bit_length()-1,(W*K).bit_length()-1)
# Lossless coordinate probes on all small words: exhaust all two-word codebooks for three bits.
words=list(product((0,1),repeat=3))
for lo,hi in product(words, repeat=2):
 for enc in product((0,1),repeat=8):
  errors=sum(sum(x!=y for x,y in zip(w,(lo,hi)[j])) for w,j in zip(words,enc))
  assert 8<=2+errors
print('All 16384 small codec/decoder combinations and all finite shape checks passed.')
```
