---
title: Bilinear noise for the Boolean moment matrix
refs: [note:pq-we-gate-table-syndrome, note:pq-we-noisy-parity, definition:WE_CircuitSAT]
tags: [witness-encryption, coding, correctness]
---

First, the noiseless auxiliary columns of the preceding gate-table scheme admit a dichotomy. If the augmented public linear system is consistent, Gaussian elimination finds some solution. Every odd selector block still has weight at most three, while every auxiliary position contributes zero noise. The parity of the found solution thus predicts the bit with correlation at least rho^(3g) >= 1/8 under the stated YES parameters. This holds on *every* consistent false instance. Inconsistency gives perfect hiding by the mask shift already proved there. Adding further noiseless linear checks of polynomial total size cannot close this gap unless their consistency already decides the language.

**Change the noise law.** For d-1 wires use all d-by-d binary matrix coordinates, with zero the homogeneous index. Let H vec(Y)=s express symmetry, Y00=1, Yii=Y0i, output one, any pinned inputs, and Y0c+Yab=1 for every NAND(a,b,c). There are O(d^2+g) sparse rows. Encrypt as (H^T a + vec(uv^T), s^T a + b), using mutually independent uniform a,u,v of the indicated dimensions. A valid trace x gives Y=(1,x)(1,x)^T, so decoding the parity with this matrix has correlation exactly 1/2. More generally for any feasible Y it has correlation Pr[Yv=0]=2^(-rank Y), by averaging over u first. This is the standard bilinear bias identity; see [Lovett](https://arxiv.org/abs/1806.09179). Raw ciphertext length is d^2+1 and the sparse mask generation, outer product and parity evaluation take O(d^2+g) bit operations in the indexed bit model.

In block form write Y with first row (1,x^T) and lower block B. Congruence elimination gives rank Y = 1 + rank(B+xx^T). The latter matrix is symmetric with zero diagonal, so its rank is even (split off a nonsingular alternating two-dimensional block until the form vanishes). Rank one is equivalent to a real satisfying trace. Hence every feasible false matrix has rank at least three and every single linear parity then has correlation at most 1/8 (infeasible parities have correlation zero). For arbitrary tests the same Parseval calculation as in the noisy-parity note gives TV <= sqrt(sum_{HY=s} 4^(-rank Y)), capped at one. Here HY means H applied to vec(Y). A minimum-rank bound alone does not control this sum.

**An exact small-instance check.** For t=NAND(x,x), f=NAND(x,t), o=NAND(f,f), the circuit is identically false. Set x=0,t=1,f=0,o=1; start with its rank-one outer product and toggle the two symmetric (x,t) entries. This gives a feasible rank-three matrix. Enumerating the full raw ciphertext laws below gives TV 17/64, exceeding both the best linear correlation 1/8 and the 1/64 packing hypothesis. Uniform linear masks can be integrated out exactly: each noisy vector is uniform on its coset of the augmented row span, so it suffices to count noise vectors modulo that span. The calculation concerns one finite circuit; it is not an asymptotic security estimate. It supplies a falsification of the proposed universal single-copy numerical bound for this exact sampler.

More generally for affine matrix systems, take H to select a k-by-k corner and s to fix that corner to the identity. Every feasible matrix has rank at least k. If t extra rows and columns are present, the ciphertext exposes the noise outside the corner. Whenever the outside-by-outside block contains a one at (i,j), the two exposed strips determine each missing noise entry by noise[a,j]*noise[i,b]. This event has probability (1-2^-t)^2. After recovering the noise, the corner and tag determine the bit. Guessing fairly otherwise gives correlation at least this probability for every k. This example concerns generic affine rank systems. A potential NO proof for circuit matrices has to account for these joint observations or use a different noise law. No fixed-game bound for arbitrary NO circuits follows.
~~~python
from collections import Counter
from fractions import Fraction
from itertools import product

def check(gates, output):
    # Wire indices start at one. Coordinate zero homogenizes affine equations.
    d = max(max(g) for g in gates)+1
    tag = 1 << (d*d)
    def entry(i,j): return 1 << (d*i+j)
    rows = [entry(0,0) ^ tag, entry(0,output) ^ tag]
    rows += [entry(i,j) ^ entry(j,i) for i in range(d) for j in range(i)]
    rows += [entry(i,i) ^ entry(0,i) for i in range(1,d)]
    rows += [entry(0,c) ^ entry(a,b) ^ tag for a,b,c in gates]
    pivots = {}
    def reduce(v):
        for i in sorted(pivots,reverse=True):
            if v>>i & 1: v ^= pivots[i]
        return v
    for row in rows:
        v = reduce(row)
        if v: pivots[v.bit_length()-1]=v
    delta = reduce(tag)
    counts = Counter()
    for u,v in product(range(1<<d), repeat=2):
        noise = sum(v << (i*d) for i in range(d) if u>>i & 1)
        counts[reduce(noise)] += 1
    keys = set(counts) | {x^delta for x in counts}
    return Fraction(sum(abs(counts[x]-counts[x^delta]) for x in keys),
                    2*sum(counts.values()))
circuits=[([(1,1,2)],2), ([(1,1,2),(1,2,3),(3,3,4)],4)]
print([check(g,o) for g,o in circuits])
assert [check(g,o) for g,o in circuits] == [Fraction(1,2),Fraction(17,64)]
~~~
