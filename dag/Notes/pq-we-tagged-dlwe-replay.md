---
title: Reproducible degree, noisy label-product, and public opening checks
refs: [note:pq-we-tagged-dlwe-switch]
tags: [witness-encryption, decomposed-lwe, experiment]
---

Run the following Python 3 program without external libraries. It tests the switch algebra with independently uniform headers and bounded errors. The security proof treats the structured Decomposed-LWE distribution separately. The exhaustive checker uses tiny parameters to verify the counting argument. No experiments assess quantum hardness or machine time.

```python
from itertools import product
from math import comb, gcd
from random import Random
rng=Random(168)
p,q,k=101,1000003,3
ell=q.bit_length()
B=2
def nearest(x,y):
    return (2*x+y)//(2*y)
def tag(n,i,b):
    return 3*n-i if b else i
for n in range(2,33):
    tags=[(i,b,tag(n,i,b)) for i in range(1,n+1) for b in [0,1]]
    ds={u+v for i,b,u in tags for j,c,v in tags if i!=j or b==c}
    assert ds==set(range(2,6*n-1))-{3*n}
    assert len(ds|{u for _,_,u in tags})==6*n-3
n=8;M=3*n
tags=[(i,b,tag(n,i,b)) for i in range(1,n+1) for b in [0,1]]
assert (1+3*(p-1))+6*ell*B < q/p
for loop in range(50):
    tau=rng.randrange(1,p); sk=[rng.randrange(q) for _ in range(k)]
    def dot(h):
        return sum(a*b for a,b in zip(h,sk))
    T=lambda u: pow(tau,u,p)
    rows={}
    labels={}
    for i,b,u in tags:
        a,m=rng.randrange(p),rng.randrange(p)
        labels[u]=m
        rows[u]=(a,(m-a*T(u))%p)
    ds=(set(range(1,6*n-1))-{M})
    bank={}
    for e in sorted(ds):
        for l in range(ell):
            h=[rng.randrange(q) for _ in range(k)]
            bank[e,l]=(h,(dot(h)+2**l*T(e)+rng.randrange(-B,B+1))%q)
    for i,b,u in tags:
        for j,f,v in tags:
            if i==j and b!=f:continue
            a,c=rows[u]; b0,d=rows[v]
            hs=[c*d,a*d,c*b0,a*b0]
            z=[nearest(q*(h%p),p) for h in hs]
            V=z[0]; U=[0]*k
            for dgr,coef in zip((u,v,u+v),z[1:]):
                for l in range(ell):
                    if (coef>>l)&1:
                        h,y=bank[dgr,l]
                        V+=y;U=[a+b for a,b in zip(U,h)]
            result=nearest(p*((V-dot(U))%q),q)%p
            assert result==labels[u]*labels[v]%p
# Exhaustive tiny public-check ideal game: arbitrary fixed headers, zero cutoff.
q0=5
for headers in product(range(q0),repeat=3):
    good=sum(any(all((y-s*h)%q0==0 for h,y in zip(headers,ys)) for s in range(q0))
             for ys in product(range(q0),repeat=3))
    assert good<=q0
# A linear combination of the first two signed moments does distinguish the mixed triple.
assert 3+(24-2)+4==1+(24-1)+5
for i,j,k0 in product(range(1,9),repeat=3):
    assert ((i+k0-j)**2-(i*i+k0*k0-j*j))%101 == (2*(i-j)*(k0-j))%101
    assert (((i+k0-j)**2-(i*i+k0*k0-j*j))%101==0)==(j==i or j==k0)
p0=2**255-19;q0=2**521-1
n=4224;D=6*n-3
assert gcd(3*n,p0-1)==12
assert ((1+3*(p0-1))+6*521*2**149)*p0<q0
assert (4*comb(n,2),4*comb(n,2)*121,D*521**2,257*D*521**2)==(35675904,4316784384,6878586381,1767796699917)
print('31 exact dictionaries, 12000 successful products, 125 exhaustive checker header vectors, 512 triple tests, and production integer ledger passed')

```
