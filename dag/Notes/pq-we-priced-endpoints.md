---
title: Pricing both projected endpoints in the mixed-block WE compiler
refs: [definition:WE_CircuitSAT, note:pq-we-mixed-block-schedule, note:pq-we-tensor-rank-survival, note:pq-we-packed-columns]
tags: [witness-encryption, correctness, compilation, complexity]
---

The previous mixed-block search priced each label at the final level as a full square preimage matrix. A valid witness only needs sufficiently many terminal columns of that matrix. Reprice each partition with both endpoints projected and the interior preimages represented in their public signed range. This changes which witness bits should be grouped even with exactly the same underlying width, gap and hardness planner.

**Wire format and correctness.** Keep one specified row per root and t specified terminal columns per final label. In the one-level case apply both projections to the root. Root residues take K bits. In the preceding model an individual preimage entry is bounded in absolute value by A=z times twice (1+floor(sqrt(nwK))) on the simultaneous good event. Center every preimage residue. If b=ceil(log2(2A+1))<K, encode it by adding A and using b bits. Outside the range map to the encoding of zero. If b>=K, send the unmodified residue. This gives a total fixed-length public transformation of full ciphertexts, even on the bad event. On the good event multiplying the selected blocks returns exactly the retained part of the full integer-mod-q product. Coordinate truncation is only at the two endpoints. A wrapper for a distinguisher applies this polynomial-time transformation to the challenge, so it adds no distinguishing advantage to a full-ciphertext hiding reduction. Its runtime must be charged. Honest generation may skip omitted independent column samples, with all shared randomness sampled from the original marginal law.

For q=2^K and a fixed valid message-one witness, it suffices for one specified tensor row to survive modulo two. If independent tensor entries have maximum parity atom at most 3/4, a nonzero input row vanishes with conditional probability at most (3/4)^n per factor, by testing its n fresh columns. Thus the total extinction probability is at most H(3/4)^n. The selected row's ideal logical/tensor product then contains a unit coefficient. With an independent uniform terminal key, all t ideal outputs are independent uniform residues in this row. Under the preceding 16(residual+1)<=q inequality, all actual residues looking short implies all t ideal residues belong to intervals of relative length at most 1/4. This gives error at most H(3/4)^n+4^-t plus the simultaneous cap failure and distance from a uniform terminal key. Message zero passes on the good event. We take t=ceil((lambda+4)/2) and check n>=3(lambda+ceil(log2 H)+4). This argument bounds each fixed valid witness and does not condition the ideal terminal law on the cap event.

**Costs.** Write B_i for the actual alphabet at level i. With H>=2 the root contributes K B_1 m bits. The other levels draw C=m sum_(1<i<H) B_i + t B_H columns. Their wire cost is m C min(K,b) bits. One-path dense decoding takes (H-2)m²+mt modular multiply-adds, plus unpacking, comparisons and witness processing. In the one-level case the cost is K B_1 t and direct shortness testing. Shared setup, target formation and key generation remain outside these counts. For fixed first and last block lengths, the middle block lengths can be sorted increasingly by the preceding exchange argument: both endpoints and the sum of interior arities stay fixed, while required K cannot increase; the signed bit width is also nondecreasing in K. Enumerate both endpoints and interior multisets for the exact minimum at fixed maximum bits per block. The number of such shapes is polynomial in witness length at a fixed cap. Search and sizing use the *full* distribution's security parameters, including omitted columns.

**24-bit control.** Use the preceding width 24, target exponent 64, alternative gap policy, maximum block length ten and n=K². All feasible candidate shapes in this control pass the single-row survival check. The previous raw optimum (10,7,7) at K=1058 cost 8.7530e26 bits. Keeping this shape but projecting and packing gives 1.1168e25 bits. The new payload optimum is (10,4,10) at K=1036. With 34 terminal columns and 27-bit signed preimage entries it costs 1.2306e24 bits, 853,965,850,624 preimage columns and at most 2.8487e21 dense modular multiply-adds. In the same projected format (10,7,7) takes 7,276,260,020,480 columns and 3.2314e21 multiply-adds. The last block can now absorb ten bits cheaply because each of its 1024 labels only needs 34 columns. These are conditional resource accounts, not secure parameters or wall-clock benchmarks. The earlier short-design and evasive-LWE premises and implementation bounds remain necessary.

The listing compares the restricted search with exhaustive ordered search on small inputs, tests 19,437 codec cases including out-of-range inputs, and verifies 140 projected products against full matrix products. Run it from the DAG root.

~~~python
from pathlib import Path
from math import isqrt
from functools import lru_cache

def listing(slug):
    return Path('dag/Notes/pq-we-'+slug+'.md').read_text().split('~~~python\n',1)[1].split('\n~~~',1)[0]

env={'__name__':'planner'}
exec(listing('stage-gap-search'),env)
def layouts(bits,cap):
    def middle(left,minimum):
        if left==0:yield ()
        for size in range(minimum,min(left,cap)+1):
            for rest in middle(left-size,size):
                yield (size,)+rest
    if bits<=cap:yield (bits,)
    for first in range(1,min(bits-1,cap)+1):
        for last in range(1,min(bits-first,cap)+1):
            for mid in middle(bits-first-last,1):
                yield (first,)+mid+(last,)

@lru_cache(None)
def account(shape):
    B=[1<<s for s in shape]
    H=len(B)
    w,lam=24,64
    (K,n,_,raw),_=env['solve'](B,w,lam,2,'budget')
    m=2*n*w*K
    t=(lam+5)//2
    assert t<=m and n>=3*(lam+env['lg'](H)+4)
    z=lam+env['lg'](H*m)+8
    bound=z*2*(isqrt(n*w*K)+1)
    b=min(K,(2*bound).bit_length())
    columns=sum(B[1:-1])*m+(B[-1]*t if H>1 else 0)
    roots=B[0]*(m if H>1 else t)
    projected=K*(roots+columns*m)
    packed=K*roots+b*columns*m
    work=(max(0,H-2)*m*m+m*t) if H>1 else 0
    return packed,columns,work,K,b,shape,projected,raw

def ordered(n,c):
    if n==0:yield ()
    for s in range(1,min(n,c)+1):
        for rest in ordered(n-s,c):yield (s,)+rest

for nbits in range(1,10):
    assert min(map(account,layouts(nbits,4)))==min(map(account,ordered(nbits,4)))
for cap in (6,8,10):
    print(cap,min(map(account,layouts(24,cap))))
print('old shape',account((10,7,7)))

# Signed packing or modular fallback, with a total map outside the cap.
def encode(x,K,A):
    q=1<<K
    r=x%q
    if (2*A).bit_length()>=K:return r
    c=r-q if r>=q//2 else r
    return c+A if abs(c)<=A else A

def read(v,K,A):
    return v if (2*A).bit_length()>=K else v-A

checks=0
for K in range(1,8):
    for A in range(1,20):
        for x in range(-2*(1<<K),2*(1<<K)+1):
            v=encode(x,K,A)
            assert v.bit_length()<=min(K,(2*A).bit_length())
            if abs(x)<=A:assert (read(v,K,A)-x)%(1<<K)==0
            checks+=1
print("codec checks",checks)

from random import Random
from itertools import product
rng=Random(1701)
def multiply(row,mat,q):
    return [sum(a*b for a,b in zip(row,col))%q for col in zip(*mat)]

paths=0
for shape in ((2,3),(4,2,4),(2,4,2,2)):
    for K in (4,10):
        q=1<<K
        A=9
        m=5
        root=[[[rng.randrange(q) for _ in range(m)] for _ in range(3)] for _ in range(shape[0])]
        layers=[[[[rng.randint(-A,A) for _ in range(m)] for _ in range(m)] for _ in range(labels)]
                for labels in shape[1:]]
        wire=[[[[encode(x,K,A) for x in r[:2 if i==len(layers)-1 else m]]
                 for r in mat] for mat in layer] for i,layer in enumerate(layers)]
        for word in product(*(range(labels) for labels in shape)):
            full=root[word[0]]
            retained=full[0]
            for layer,enc,s in zip(layers,wire,word[1:]):
                full=[multiply(r,layer[s],q) for r in full]
                retained=multiply(retained,[[read(v,K,A) for v in r] for r in enc[s]],q)
            assert retained==full[0][:2]
            paths+=1
print("projected products",paths)
~~~
