---
title: Reproduce the nine-bit aggregate packet and ternary overlap experiments
refs: [note:pq-we-common-address-aggregate]
tags: [witness-encryption, reproducibility]
---

Self-contained Python 3 replay. It enumerates all records in both message worlds and emits both 4096-gate registered fixtures.

```python
from itertools import product
from collections import Counter
from random import Random

def audit(repair,yes):
    hist=[Counter(),Counter()]
    for coins in product(range(2),repeat=8+int(repair)):
        a0,ax,b0,by,c0,cx,cy,cxy=coins[:8]
        bxy=coins[8] if repair else 0
        cells=[(x,y) for x,y in product(range(2),repeat=2)
               if (1-x if yes else x) or y]
        cv=lambda x,y:c0^(cx*x)^(cy*y)^(cxy*x*y)
        C=tuple(cv(x,y) for x,y in cells)
        for b in (0,1):
            H=(b^a0^b0^c0,ax^cx,by^cy,bxy^cxy)
            h=lambda x,y:H[0]^(H[1]*x)^(H[2]*y)^(H[3]*x*y)
            frame=(a0,b0,*C,*H)
            hist[b][frame]+=1
            if not repair and not yes:
                assert h(0,1)^h(1,0)^h(1,1)^a0^b0^C[0]^C[1]^C[2]==b
            if yes:
                assert h(0,0)^a0^b0^C[cells.index((0,0))]==b
    assert (hist[0]==hist[1])==(repair and not yes)
    if repair and not yes: assert len(hist[0])==512 and set(hist[0].values())=={1}
    else: assert hist[0].keys().isdisjoint(hist[1])
    print('repair',repair,'YES',yes,'atoms',len(hist[0]))
for repair,yes in product(range(2),repeat=2):audit(repair,yes)
def raw(yes):
    g=[]
    def N(a,b):g.append((a,b));return 128+len(g)
    def neg(a):return N(a,a)
    def AND(a,b):return neg(N(a,b))
    def OR(a,b):return N(neg(a),neg(b))
    def XOR(a,b):c=N(a,b);return N(N(a,c),N(b,c))
    h=3;k=4
    for i in range(2037):
        h=N(h,3+(7*i)%126);k=N(k,3+(11*i)%126)
    x=XOR(1,h);y=XOR(2,k)
    a=neg(x);b=neg(y);c=OR(a if yes else x,y)
    out=AND(AND(a,b),c)
    before=len(g); gap=4096-before
    if gap%2:
        v=neg(out);t=N(out,v);out=N(v,t)
    while len(g)<4096:out=neg(neg(out))
    assert len(g)==4096
    live={out}
    for j,(a,b) in reversed(list(enumerate(g,129))):
        assert j in live;live.update((a,b))
    def run(inp):
        z=[1]+list(inp)
        for a,b in g:z.append(1-z[a]*z[b])
        return z[x],z[y],z[out]
    return g,before,run
rng=Random(172)
for yes in (False,True):
    g,before,run=raw(yes)
    for t in range(32):
        tail=[rng.getrandbits(1) for _ in range(126)]
        o=[run([a,b]+tail) for a,b in product(range(2),repeat=2)]
        assert len(set((x,y) for x,y,z in o))==4
        assert all(bool(z)==(yes and not x and not y) for x,y,z in o)
    print('fixture',yes,'before padding',before,'raw bits',sum(4*a+2*b+3 for a,b in g))

for yes in (False,True):
    counts=[Counter(),Counter()]
    for seeds in product(range(3),repeat=3):
        for beta in (0,1):
            vals=[]
            for x,y in product(range(2),repeat=2):
                v=(x,y,int(not ((1-x if yes else x) or y)))
                S=sum(v)%3
                vals.append((beta+S*sum(a*b for a,b in zip(v,seeds)))%3)
            a,b,c,d=vals
            coeff=(a,(c-a)%3,(b-a)%3,(d-b-c+a)%3)
            counts[beta][coeff]+=1
    assert (counts[0]==counts[1])==(not yes)
    print('ternary, YES',yes,'atoms',len(counts[0]))
for m in (3,5):
    for x in (0,1):
        v=(1,1,1,x,x)
        if sum(v)%m==0:
            assert all((a*pow(sum(v),m-2,m))%m==0 for a in v)

```
