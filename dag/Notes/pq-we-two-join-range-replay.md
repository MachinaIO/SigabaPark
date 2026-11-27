---
title: Executable LWE label routing and final payload replay
refs: [note:pq-we-two-join-range-router]
tags: [witness-encryption, reproducibility]
---

The following Python 3 replay uses an intentionally tiny generator to test actual serialized row bodies, the public check values and decryption, followed by the exact ledger for the illustrative parameters.

```python
from collections import defaultdict
from itertools import product
from random import Random
def graph(n):
    rows=[]
    def add(dest,*src):rows.append((dest,src))
    for role in ('A','C'):
        for j in range(1,n):
            add((role,'L',j),(role,j-1))
            if j>1:add((role,'L',j),(role,'L',j-1))
        for j in reversed(range(n-1)):
            add((role,'R',j),(role,j+1))
            if j<n-2:add((role,'R',j),(role,'R',j+1))
    for role in ('A','C'):
        for j in range(n):
            dest=('K',j) if role=='A' else ('T',)
            other=('J',j) if role=='A' else ('K',j)
            if j>0:add(dest,other,(role,'L',j))
            if j<n-1:add(dest,other,(role,'R',j))
    return rows
def replay(n,seed):
    rng=Random(seed);rows=graph(n)
    inc=defaultdict(list); V=set()
    for a,(v,ps) in enumerate(rows):
        V.add(v)
        for p in ps: inc[p].append(a);V.add(p)
    assert (len(V),len(rows),sum(map(len,inc.values())))==(8*n-3,12*n-16,16*n-20)
    # Toy q=256, n_LWE=2, m=8, CBD(1): 32 -> 64 bits.
    mat=[[rng.randrange(256) for _ in range(2)] for j in range(8)]
    def G(k):
        s=[k>>(8*j)&255 for j in range(2)]
        z=sum(((sum(x*y for x,y in zip(a,s))+((k>>(16+2*i)&1)-(k>>(17+2*i)&1)))&255)<<(8*i) for i,a in enumerate(mat))
        return (z&0xffffffff,z>>32)
    def expand(seed,count):
        if count==1:return [seed]
        a,b=G(seed);h=count//2
        return expand(a,h)+expand(b,count-h)
    def emit(v,k):
        outputs=expand(k,len(inc[v])+1+(v==('T',)))
        return dict(zip(inc[v],outputs)),G(outputs[len(inc[v])]),outputs[-1]&1
    K={v:rng.getrandbits(32) for v in sorted(V,key=repr)}
    parts={v:emit(v,k) for v,k in K.items()}
    tags={v:p[1] for v,p in parts.items()}
    bodies=[]
    for a,(v,ps) in enumerate(rows):
        c=K[v]
        for p in ps:c^=parts[p][0][a]
        bodies.append(c)
    payload=1^parts[('T',)][2]
    seen=valid=0
    for masks in product(range(1<<n),repeat=3):
        opened={ (r,j):K[r,j] for r,m in zip(('A','J','C'),masks) for j in range(n) if (m>>j)&1 }
        masks_at={}
        def insert(v,k):
            ins,tag,bit=emit(v,k);assert tag==tags[v]
            opened[v]=k;masks_at[v]=ins
            return bit
        for v,k in list(opened.items()):insert(v,k)
        for a,(v,ps) in enumerate(rows):
            if v not in opened and all(p in opened for p in ps):
                out=bodies[a]
                for p in ps:out^=masks_at[p][a]
                d=insert(v,out)
                if v==('T',):assert (payload^d)==1
        truth=any(i!=j and k!=j and masks[0]>>i&1 and masks[1]>>j&1 and masks[2]>>k&1
                  for i,j,k in product(range(n),repeat=3))
        assert (('T',) in opened)==truth
        valid+=truth;seen+=1
    print("n, cases, reachable",n,seen,valid)
for n in (2,3,4):replay(n,169+n)
for n in (128,4224):
    V=8*n-3;E=12*n-16;P=16*n-20;g=P+V+1
    print(n,V,E,P,g,(1024*4096*16)+(E+2*V)*32768+1,g*(1024*4096))

```
