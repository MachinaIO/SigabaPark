---
title: Replay the registered NAND frontend and conditioned systems
refs: [note:pq-we-conditioned-joint-headers]
tags: [witness-encryption, reproducibility]
---

The following self-contained Python 3 program checks the real wire-zero convention, default-one reads, exact diamond recognition and liveness, authenticates covered wire values and derives the branch ranks of the full-size fixture. The shear test checks native images in small dimension.

```python
"""Registered wire 0 and unavailable predecessors read one. No dependencies."""
from itertools import product
from random import Random

def normalized(n, gates):
    return [(a if 0 <= a < n+1+i else 0, b if 0 <= b < n+1+i else 0)
            for i,(a,b) in enumerate(gates)]

def frontend(n, gates):
    raw = normalized(n,gates)
    ir = {}
    for i,(a,b) in enumerate(raw,n+1):
        kind = 'nand'
        if n < a < i and n < b < i:
            pa,pb = raw[a-n-1],raw[b-n-1]
            for t in set(pa).intersection(pb):
                u = pa[1] if pa[0]==t else pa[0]
                v = pb[1] if pb[0]==t else pb[0]
                if n < t < min(a,b) and max(u,v)<t and sorted(raw[t-n-1])==sorted([u,v]):
                    kind,a,b = 'xor',u,v
                    break
        ir[i]=kind,a,b
    live={n+len(gates)}
    for i in reversed(ir):
        if i in live:
            live.update(ir[i][1:])
    return {i:op for i,op in ir.items() if i in live}

def choose(ir):
    edges=[(a,b) for kind,a,b in ir.values() if kind=='nand' and a!=b and a and b]
    cover=set()
    for a,b in edges:
        if a not in cover and b not in cover:
            cover.update((a,b))
    for x in sorted(cover):
        if all((a!=x and a in cover) or (b!=x and b in cover) for a,b in edges):
            cover.remove(x)
    return sorted(cover)

def residual(n,ir,chosen,z):
    const=1<<n
    f={0:const,**{i+1:1<<i for i in range(n)}}
    force=dict(zip(chosen,z))
    for i,(kind,a,b) in ir.items():
        p,q=f[a],f[b]
        if kind=='xor': out=p^q
        elif a==b or q==const: out=const^p
        elif p==const: out=const^q
        elif a in force: out=const^(q if force[a] else 0)
        else: out=const^(p if force[b] else 0)
        f[i]=out
    return [f[a]^(const if force[a] else 0) for a in chosen]+[f[max(ir)]^const]

def eval_raw(n,gates,w):
    wires=[1]+[w>>j&1 for j in range(n)]
    for a,b in normalized(n,gates):
        wires.append(1^(wires[a]&wires[b]))
    return wires

def rank(cols):
    basis={}
    for x in cols:
        while x:
            i=x.bit_length()-1
            if i not in basis:
                basis[i]=x
                break
            x ^= basis[i]
    return len(basis)

def ranks(n,ir,chosen):
    ans=[]
    for z in product((0,1),repeat=len(chosen)):
        rows=residual(n,ir,chosen,z)
        cols=[sum(((v>>i)&1)<<j for j,v in enumerate(rows)) for i in range(n)]
        ans.append(rank(cols))
    return ans

def fixture():
    n=128
    gates=[]
    def nand(a,b):
        gates.append((a,b))
        return n+len(gates)
    def xor(a,b):
        c=nand(a,b)
        return nand(nand(a,c),nand(c,b))
    v=2
    for i in range(3,129):
        v=xor(v,i)
    while len(gates)<4094:
        nand(0,0)
    v=nand(1,v)
    nand(v,v)
    return gates

def validate():
    rng=Random(4191)
    for _ in range(210):
        n=4
        gates=[(rng.randrange(17),rng.randrange(17)) for _ in range(12)]
        ir=frontend(n,gates)
        chosen=choose(ir)
        for z in product((0,1),repeat=len(chosen)):
            rows=residual(n,ir,chosen,z)
            for w in range(1<<n):
                wires=eval_raw(n,gates,w)
                actual=wires[-1] and all(wires[j]==v for j,v in zip(chosen,z))
                assert all((r&(w|(1<<n))).bit_count()%2==0 for r in rows)==bool(actual)
    gates=fixture()
    ir=frontend(128,gates)
    chosen=choose(ir)
    assert len(gates)==4096 and len(chosen)==1 and ranks(128,ir,chosen)==[1,2]
    assert sum(op[0]=='xor' for op in ir.values())==126
    for k in range(1,6):
        for z in range(1<<k):
            for w in range(1<<(k+1)):
                v=w^((w>>1)&z)
                raw=(v<<1) | ((v&z).bit_count()%2)
                aligned=raw^((v&z).bit_count()%2)
                assert aligned==v<<1 and ((raw&((z<<1)|1)).bit_count()%2)==0
    print('210 raw registered-format circuits, all branches and witnesses; fixture ranks [1,2]; shears k=1..5 verified.')

if __name__=='__main__':
    validate()
```
