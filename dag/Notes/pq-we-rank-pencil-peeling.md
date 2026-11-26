---
title: Composing fixed LWE hops on a shared rank pencil and deleting the resolved columns
refs: [definition:WE_CircuitSAT, note:pq-we-direct-minor-lwe]
tags: [witness-encryption, reduction, rank, complexity]
---

Use the preceding note's ciphertext (S,Y), with Y_i=S M_i r+e_i in the real mode. Keep the single shared uniform S, the single shared short iid r, and independent errors. For an active set A of output indices, let private coordinates of i be those j for which every other active M_l has zero column j. Call i eligible if M_i restricted to its private coordinates has rank at least the fixed short-secret dimension h>=2. Find h independent private columns J by elimination. Remove i and repeat. Computing the active supports and finite-field ranks at most k times over k candidates takes polynomial time. Eligibility is monotone under deletion of other indices. Any maximal run leaves the same residual set: induct along one run, noting that the first removed item still in another run's terminal set would have been eligible there. Reverse the two runs for equality.

**Shared-ciphertext hybrids.** In a hybrid the removed output columns are independent uniform, and the active columns retain their original joint law given S. Embed one fixed t-by-h decisional short-secret LWE challenge (B,z) at an eligible i. With P=M_i[:,J], draw S uniformly in the fiber SP=B using the previous left-inverse formula. Draw just r outside J. All other active outputs are now computable honestly since their omitted columns vanish. Use z plus the outside-J contribution for Y_i and sample the previously removed outputs uniformly. Real LWE supplies exactly the common secret coordinates and fresh error required for the active joint law. A uniform z makes only Y_i independent uniform. All columns use the same S even if their output images coincide. After p removals the total advantage difference is at most p times the single-game advantage at the wrapper's actual runtime. The same fixed q,h,t, secret and error law work at every hop. If a residual remains this proves no security for its real columns.

For a strict separation from the one-shot sufficient condition, take k>=2 and d=kh, partition input coordinates into k blocks of h, and let each M_i copy block i into the SAME first h output coordinates. Every index is eligible. The concatenation sought by the previous note has rank at most h for every choice of common columns and even for every common change of input basis. The peeled family can also have genuinely shared secret coordinates by adjoining an extra column used by every matrix while keeping disjoint private blocks. The wrapper simulates that extra coordinate once.

**A direct efficiency consequence.** For every combination with a nonzero coefficient on any removed generator, choose its earliest such generator in the run. On that step's J the combination equals a_i P, which has rank h. Hence every rank-one witness has zero coefficients on *all* removed outputs. Conversely every residual rank-one witness extends by zeros and gives precisely the same matrix. One can therefore encrypt only the residual columns, project the witness coefficients, and retain exactly the old witness test Ya-cSu on valid paths under a coupling. Draws of S and r keep their original law. Zero coordinate columns shared by all residual matrices may also be skipped when forming products. For p removed indices and a fixed public statement, the ciphertext saves pt field elements, encryption skips p products and p noise columns, and dense decryption saves pt scalar multiply-adds in Ya. Include public preprocessing and witness conversion in total runtime. For an empty residual the rank-one YES predicate is publicly impossible; for a mixed pencil the residual still needs its own security proof. A security proof for the full ciphertext also transfers by simple projection. These statements assume the earlier rank-one witness interface, including all bounds needed for decoding.

**Limit for CircuitSAT.** If every false circuit compiled in polynomial time to a fully peelable pencil and every true circuit supplied a rank-one witness, running the polynomial-time peel test would decide CircuitSAT. Thus this *specific* attempt to compose local steps across the public outputs would require P=NP for full coverage. A hybrid over rejecting witness assignments would require a different construction and a separate proof that those hybrids preserve correlations. The rank test and reduction do not implement such a hybrid.

The test compares greedy deletion with all maximal orders on random small matrices. A second check exhausts the joint simulation for a shared coordinate, overlapping output images, binary secrets and binary errors over F_3.
~~~python
from collections import Counter
from itertools import product
from random import Random

def rank(columns):
    # Binary columns packed as integers, used for the order check.
    basis = {}
    for x in columns:
        while x and x.bit_length() in basis:
            x ^= basis[x.bit_length()]
        if x:
            basis[x.bit_length()] = x
    return len(basis)

def choices(mats, active):
    return [i for i in active if rank([
        v for j,v in enumerate(mats[i])
        if all(l==i or mats[l][j]==0 for l in active)])>=2]

def terminals(mats,active):
    eligible = choices(mats,active)
    if not eligible:
        return {tuple(active)}
    return set.union(*(terminals(mats,[l for l in active if l!=i]) for i in eligible))

rng = Random(171)
for case in range(500):
    mats = [[rng.randrange(4) if rng.random()<0.45 else 0 for j in range(8)]
            for i in range(4)]
    assert len(terminals(mats,list(range(4))))==1

# The first hop uses B=(s0,s1). Each output copies a private two-bit
# block and adds the common fifth bit into its first output coordinate.
# Only the two active public coordinates of the row are shown.
honest, real, hybrid, ideal = (Counter() for _ in range(4))
bits = list(product(range(2),repeat=2))
for s in product(range(3),repeat=2):
    for u,v in product(bits,repeat=2):
        for g,e,f in product(range(2),repeat=3):
            first = (s[0]*(u[0]+g)+s[1]*u[1]+e)%3
            second = (s[0]*(v[0]+g)+s[1]*v[1]+f)%3
            honest[s,first,second] += 1
            response = (sum(a*b for a,b in zip(s,u))+e)%3
            real[s,(response+s[0]*g)%3,second] += 1
            for z in range(3):
                hybrid[s,z,second] += 1
                ideal[s,(z+s[0]*g)%3,second] += 1
assert real==honest and ideal==hybrid
print("500 order checks",sum(real.values()),sum(ideal.values()))
~~~
