---
title: Optimizing root and suffix block lengths with a common hardness envelope
refs: [definition:WE_CircuitSAT, note:pq-we-stage-gap-search, note:pq-we-costed-block-alphabet]
tags: [witness-encryption, complexity, compilation]
---

A B-way root sends B residue blocks of size n by m. A later B-way level sends B preimage blocks of size m by m. The asymmetry changes the best way to partition a public witness order even at fixed depth and maximum alphabet. Price each candidate using the least feasible K in the preceding note, common logical width w and the full alphabet of every block. A block of s consecutive bits has B=2^s fresh labels. Logical fusion is valid for the earlier live Boolean programs. Repartitioning changes cut positions, not witness order.

**Exchange argument for the common-width envelope.** Fix the first block and the multiset of later block lengths. At fixed K the dense price is identical for all permutations. Swapping an adjacent inverted pair of suffix lengths to increasing order decreases one partial prefix product P_i and preserves all others. H, terminal P_H, maximum alphabet, w and the scale S are invariant. The cumulative hop loss, local gap bounds, root noise and required K cannot increase under either gap policy in the preceding planner. Therefore the least feasible K, the corresponding payload, sampled columns and dense Dec count cannot increase. Sort the suffix, then enumerate the possible root choices and suffix multisets. This certifies the least payload under the shape-only envelope. An implementation with actual cut-dependent widths, per-stage distributions, or prefix energies needs a fresh comparison. Realizing the sorted shape means assigning new boundaries to the original bits.

**Polynomial compilation.** With a fixed cap c on bits per block there are at most c(N+1)^c canonical shapes for N bits, so even the exact search is polynomial at fixed c. A lighter search tries each root length and remaining block count, distributing the suffix bits as evenly as possible in increasing order. It prices O(cN) shapes and is polynomial even for logarithmic c; making each chosen table is then polynomial as well. This lighter search matched the exhaustive optimum in the reported 24-bit controls. No general optimality claim is made for it. Neither search needs to construct lattice keys to evaluate a candidate.

**Same-cap control.** Use N=w=24, lambda=64, inverse hardness exponent two and the previous alternative gap policy. Each triple below consumes the same 24 bits in three levels, with maximum alphabet 1024. The costs are conditional accounts per encrypted bit.

| Bits read per level | Modulus exponent K | Raw payload bits | Preimage columns | Dense Dec multiply-adds |
| --- | ---: | ---: | ---: | ---: |
| 10,10,4 | 1079 | 4.0801e27 | 6.2710e13 | 8.4661e27 |
| 10,4,10 | 1036 | 3.0693e27 | 5.5508e13 | 6.1149e27 |
| 10,7,7 | 1058 | 8.7530e26 | 1.4553e13 | 7.2343e27 |

The smallest-payload schedule among all admissible depths is (10,7,7). It uses 256 nonroot labels instead of 1040 under the first schedule. The smallest K of the three examples gives the lowest dense Dec count of the three but a larger payload than the optimum. At cap seven the payload optimum is (7,5,6,6). At caps three, four, six and eight the payload optima divide 24 evenly, for both previous gap policies. These comparisons retain the assumed common quantitative bounds on hops at their respective prefix sizes. The altered matrix distributions still require the corresponding quantum hardness and sampler premises. Reported sizes are far from practical and the finite controls do not establish general WE security.

The listing tests the exchange-based minimum against all ordered compositions for lengths one through nine and both policies. It also constructs the 1024,128,128 logical label tables for a width-24 diagonal clause program and checks all terminal coordinates against the unblocked clause evaluator on 2,052 word/message trials. This last test checks the logical compiler only.

~~~python
from pathlib import Path
from functools import lru_cache

source = Path('dag/Notes/pq-we-stage-gap-search.md').read_text()
env = {'__name__':'planner'}
exec(source.split('~~~python\n',1)[1].split('\n~~~',1)[0],env)

def schedules(left,lo,cap):
    if not left:
        yield ()
    for value in range(lo,min(left,cap)+1):
        for rest in schedules(left-value,value,cap):
            yield (value,)+rest

def balanced_shapes(bits,cap):
    for first in range(1,min(bits,cap)+1):
        left=bits-first
        if not left:
            yield (first,)
        for slots in range(1,left+1):
            low,extra=divmod(left,slots)
            if low+bool(extra)<=cap:
                yield (first,)+(low,)*(slots-extra)+(low+1,)*extra

@lru_cache(None)
def price(shape,policy):
    B=[1<<v for v in shape]
    (K,n,_,payload),_=env['solve'](B,24,64,2,policy)
    m=2*n*24*K
    return payload,sum(B[1:])*m,(len(B)-1)*n*m*m,K,shape

def all_shapes(bits,cap):
    for first in range(1,min(bits,cap)+1):
        for rest in schedules(bits-first,1,cap):
            yield (first,)+rest

def brute(left,cap):
    if not left:
        yield ()
    for v in range(1,min(cap,left)+1):
        for rest in brute(left-v,cap):
            yield (v,)+rest

for policy in ('square','budget'):
    for cap in (3,4,6,8):
        candidates=list(all_shapes(24,cap))
        best=min(price(s,policy) for s in candidates)
        fast=min(price(s,policy) for s in balanced_shapes(24,cap))
        print(policy,cap,len(candidates),best,fast==best)
    for bits in range(1,10):
        assert min(price(s,policy) for s in all_shapes(bits,4))==min(
            price(s,policy) for s in brute(bits,4))

for cap in (7,10):
    best=min(price(s,'budget') for s in all_shapes(24,cap))
    assert best==min(price(s,'budget') for s in balanced_shapes(24,cap))
    print("mixed",cap,best)

from random import Random
rng=Random(776)
clauses=[rng.sample(range(24),3) for _ in range(23)]
shape=(10,7,7)
# A diagonal entry survives exactly while its clause has seen no true literal.
tables=[]
start=0
for s in shape:
    table=[]
    for local in range(1<<s):
        mask=1
        for j,clause in enumerate(clauses,1):
            if not any(start<=v<start+s and (local>>(v-start))&1 for v in clause):
                mask |= 1<<j
        table.append(mask)
    tables.append(table)
    start+=s
for word in [0,(1<<24)-1]+[rng.getrandbits(24) for _ in range(1024)]:
    for mu in (0,1):
        row=((1<<24)-2)|mu
        start=0
        for s,table in zip(shape,tables):
            row &= table[(word>>start)&((1<<s)-1)]
            start+=s
        expected=mu+sum((1<<j) for j,c in enumerate(clauses,1)
                        if not any((word>>v)&1 for v in c))
        assert row==expected
~~~
