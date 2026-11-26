---
title: Exact binary key addition in a clause-restricted evaluator
refs: [note:pq-we-clause-subtree-rekey, note:pq-we-clause-restriction-spaces]
tags: [witness-encryption, reduction, correctness]
---

A public-key interface one might try in place of the clause evaluator oracle is to give one constrained key per clause, usable on traces satisfying that clause. Consider the following specific template. A common public setup independent of the clause contents defines F_K(x)=A_x K, with K in GF(2)^d, output in GF(2)^l, and public polynomial-time evaluation under chosen keys. A_x may be an arbitrary nonlinear function of x and of the setup. Its columns can be computed from unit keys. For bit zero sample clause keys whose sum is zero; for bit one sample independent uniform keys (so their sum is uniform). Give only their restrictions to their respective satisfying domains. At a witness the sum of evaluations is zero for bit zero and is nonzero for bit one with probability 1-2^(-rank A_x). This is the proposed decoder's completeness requirement. Exact binary key-linearity is stronger than the almost-homomorphism and single-key guarantees in [Brakerski and Vaikuntanathan](https://iacr.org/archive/tcc2015/90150001/90150001.pdf). The following calculation is about the template, not that construction.

**A false formula for the public interface.** For an n-bit word w, take n unit clauses fixing the bits to w and one wide clause that excludes only w. This formula is unsatisfiable. At w the units all authorize their outputs. The wide clause authorizes F_K(x) everywhere except w. Even treating its restricted key as a black box suffices to interpolate its output on most targets when d is polynomial and the address space is exponentially large. This statement allows fresh random setup *after* the target is fixed.

Draw M uniform n-bit training words and take w uniform and independent for the analysis. For any fixed setup let E(x) be the subspace spanned by the rows of A_x. Among any M+1 blocks at most d are essential, meaning their removal reduces the joint dimension. To see this choose one vector from each essential block outside the sum of the others. These vectors are independent by inspecting a nonzero coefficient in any putative dependence. By exchangeability,

    Pr[E(w) is not contained in the span of the training rows] <= d/(M+1).

This holds for each setup separately. With probability at most M/2^n a training word hits w; one may abort before making an unauthorized evaluation. On the remaining good event linear elimination of the public rows expresses every output bit of F_K(w) in terms of authorized evaluations. No extraction of K or access to the internals of the restricted key is required. Add the unit-clause outputs to recover the decoder's zero/nonzero statistic. On abort output zero. For the zero-message law the decoder always returns zero; for the one-message law its acceptance averaged over w is at least

    1 - E[2^(-rank A_w)] - d/(M+1) - M/2^n.

Here the uniform sum of keys is independent of the sampled words and setup (conditional on the setup). Thus some fixed false statement has at least this distinguishing gap over fresh setup and encryption randomness. For M=16d and nonzero A_w on all targets the bound is at least 1/2-1/16-M/2^n; if honest collision probability is negligible, the bound is correspondingly higher. The calculation needs 2^n much larger than M. No brute-force enumeration of the address space is involved. The conclusion assumes that restrictive keys supply the same common-family evaluations and the compiler does not first simplify this formula to a different representation.

**Boundary for a noisy proposal.** If the given oracle outputs are vectors whose *whole-vector* disagreement probability from their exact linear labels is at most eta on each authorized input, uniformly conditional on public setup and the chosen keys, the same argument loses at most (M+n)eta per message by a union bound. Small occasional failures of otherwise exact evaluations do not remove the obstruction. This does not bound interpolation of modularly rounded labels or group encodings without accessible field coordinates. A positive reduction for those models would need both correctness after adding all authorized outputs and a fixed-game argument for the joint information carried by the released keys. Merely invoking single-key off-domain pseudorandomness does not discharge either quantitative obligation.

The finite check enumerates every sequence of four input blocks for two public three-bit key families and verifies the essential-block bound. It also checks functional interpolation on every key whenever the held-out block is spanned, using only training outputs.
~~~python
from itertools import product
def feature_outputs(rows,key):
    return tuple((row&key).bit_count()%2 for row in rows)
def span(rows):
    s={0}
    for r in rows: s |= {x^r for x in s}
    return s
total=0
for family in (((1,2),(2,4),(3,5),(6,7)), ((0,0),(0,1),(2,2),(0,4))):
    for inputs in product(range(4),repeat=4):
        essential=0
        for i,x in enumerate(inputs):
            train=[r for j,y in enumerate(inputs) if i!=j for r in family[y]]
            if not set(family[x])<=span(train):
                essential+=1
                continue
            seen={}
            for key in range(8):
                obs=feature_outputs(train,key)
                val=feature_outputs(family[x],key)
                assert seen.setdefault(obs,val)==val
        assert essential<=3
        total+=1
print(total)
~~~
