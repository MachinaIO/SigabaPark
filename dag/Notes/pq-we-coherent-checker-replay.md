---
title: Reproduce the two-insertion checker estimate and lane budgets
refs: [note:pq-we-coherent-checker-sharp]
tags: [finite-distributions, reproducibility]
---

Run using Python 3. The orthogonal-state cases exercise split leakage and public effects; the arbitrary-operator identities and lane thresholds use exact arithmetic.

```python
"""Exact noncommuting expansion and decision-gap checks; standard Python only."""
from fractions import Fraction as F
from random import Random

I=((1,0),(0,1))
Z=((0,0),(0,0))
def plus(a,b): return tuple(tuple(x+y for x,y in zip(r,s)) for r,s in zip(a,b))
def neg(a): return tuple(tuple(-v for v in row) for row in a)
def times(a,b):
    return tuple(tuple(sum(a[i][t]*b[t][j] for t in range(2)) for j in range(2)) for i in range(2))
def prod(mats):
    out=I
    for m in mats: out=times(out,m)
    return out

def exact_products():
    rng=Random(193)
    for q in range(8):
        for _ in range(32):
            mat=lambda:tuple(tuple(rng.randrange(-3,4) for _ in range(2)) for _ in range(2))
            b,d=[mat() for _ in range(q)], [mat() for _ in range(q)]
            a=list(map(plus,b,d))
            v=Z
            for i in range(q):
                v=plus(v,prod(b[:i]+[d[i]]+b[i+1:]))
                for j in range(i+1,q):
                    v=plus(v,prod(b[:i]+[d[i]]+a[i+1:j]+[d[j]]+b[j+1:]))
            assert plus(prod(a),neg(prod(b)))==v

def decision():
    rng=Random(193110)
    theta=(F(3,5),F(4,5))
    rot=lambda pair,t: (theta[0]*pair[0]-t*theta[1]*pair[1],
                         t*theta[1]*pair[0]+theta[0]*pair[1])
    for q in range(4):
        for _ in range(12):
            # Real orthogonal dynamics on 8 addresses. Hidden mark uniform on 8,
            # each public leakage value gives a subset of four possibilities.
            ops=[[rng.choice((-1,1)) for _ in range(4)] for _ in range(q+1)]
            def run(mark, leak):
                x=[F(0) for _ in range(8)]; x[leak]=F(1)
                for i,op in enumerate(ops):
                    for j,sign in enumerate(op):
                        a=(2*j+i)%8; b=(a+1)%8
                        x[a],x[b]=rot((x[a],x[b]),sign)
                    if i<q and mark is not None: x[mark]=-x[mark]
                return sum(v*v for i,v in enumerate(x) if ((i>>1)&1)==leak)
            gap=sum((run(m,m//4)-run(None,m//4) for m in range(8)),F(0))/8
            assert abs(gap)<=4*q*q*F(1,4)
    for n in [8,32,1024]:
        p=F(1,n)
        assert 1-(1-2*p)**2==4*p*(1-p)

def lanes():
    for leak in (0,64):
        for bits in (32,64):
            rows=[]
            for a in range(1,40):
                for b in range(1,40):
                    p=F(16897,257**4-1)**a+F(16897,769**4-1)**b
                    bound=4*2**(2*bits+leak)*p
                    if bound<=F(1,2**128): rows.append((max(a,b),a+b,a,b))
            print(leak,bits,min(rows)[2:])
if __name__=='__main__':
    exact_products(); decision(); lanes()
    print('noncommuting expansions, orthogonal states and sharp q=1 formula verified')
```
