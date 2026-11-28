---
title: Reproduce full-size fixed RingLWE registry and finite low-digit sampler checks
refs: [note:packed-lower-ring-selector, definition:PackedRingPacket]
tags: [witness-encryption, ring-lwe, reproducibility]
---

Run the Python listings as separate files in the same directory with python3, and run the Lean listing with lake env lean from the pinned core. Numbers from evaluating H describe the classical registry entry.

### ring.py

```python
"""Exact small-ring lifting law and negacyclic scalar sample extraction."""
from itertools import product
from collections import Counter

def mul(a,b,q):
    n=len(a)
    h=[0]*n
    for i,x in enumerate(a):
        for j,y in enumerate(b):
            h[(i+j)%n] += x*y*(1 if i+j<n else -1)
    return tuple(x%q for x in h)

def translated(x,y,q,scale=1):
    return tuple((a+scale*b)%q for a,b in zip(x,y))

def main():
    n,d,p=2,2,3
    q=d*p
    def vec(m):
        return list(product(range(m),repeat=n))
    for a,t in product(vec(d),vec(p)):
        s=translated(a,t,q,d)
        for A in vec(q):
            at=mul(A,t,p)
            aa=mul(A,a,q)
            for e,u in product(vec(2),vec(d)):
                real=translated(translated(aa,u,q),translated(at,e,p),q,d)
                target=translated(translated(mul(A,s,q),e,q,d),u,q)
                assert real==target
            hist=Counter(translated(translated(aa,u,q),l,q,d) for l,u in product(vec(p),vec(d)))
            assert len(hist)==q**n and set(hist.values())=={1}
            for j,coeff in enumerate(mul(A,s,q)):
                row=[A[(j-k)%n]*(1 if k<=j else -1) for k in range(n)]
                assert sum(h*v for h,v in zip(row,s))%q==coeff
    print('all 1296 secret/header pairs; real, ideal and extracted samples verified')
if __name__=='__main__':
    main()

def external_test():
    from random import Random
    rng=Random(207)
    n,w=8,10
    q=2**w
    def randvec():
        return tuple(rng.randrange(q) for _ in range(n))
    for _ in range(300):
        s=randvec()
        bit=s[rng.randrange(n)]%2
        right=[randvec(),randvec()]
        ans=[(0,)*n,(0,)*n]
        noise=(0,)*n
        for j in range(2):
            for k in range(w):
                a=randvec()
                e=tuple(rng.randrange(-2,3) for _ in range(n))
                b=translated(mul(s,a,q),e,q)
                shift=(bit*2**k,)+(0,)*(n-1)
                col=[a,b]
                col[j]=translated(col[j],shift,q)
                z=tuple(x>>k&1 for x in right[j])
                for h in range(2):
                    ans[h]=translated(ans[h],mul(col[h],z,q),q)
                noise=translated(noise,mul(e,z,q),q)
        lhs=translated(ans[1],mul(s,ans[0],q),q,-1)
        rhs=translated(right[1],mul(s,right[0],q),q,-1)
        assert lhs==translated(noise,rhs,q,bit)
    print('300 exact external products with own low-bit messages')
if __name__=='__main__':
    external_test()
```

### more.py

```python
from itertools import product
from random import Random
import runpy
from pathlib import Path
root=Path(__file__).parent
lib=runpy.run_path(str(root/'ring.py'))
mul=lib['mul']; add=lib['translated'];r=Random(208)
for n in (2,8,16):
  w=16;q=1<<w;D=q//2
  for trial in range(90):
    s=tuple(r.randrange(q) for _ in range(n));low=tuple(x%2 for x in s)
    A=tuple(r.randrange(q) for _ in range(n));e=tuple(r.randrange(-2,3) for _ in range(n))
    v=r.randrange(2);P=add(e,(D*v,)+(0,)*(n-1),q);B=add(mul(s,A,q),P,q)
    out=[(0,)*n,(0,)*n];noise=(0,)*n
    for idx,inp in enumerate((A,B)):
      for j in range(w):
        H=tuple(r.randrange(q) for _ in range(n));E=tuple(r.randrange(-2,3) for _ in range(n))
        Y=add(mul(s,H,q),E,q);col=[H,Y];col[idx]=add(col[idx],low,q,1<<j)
        z=tuple(x>>j&1 for x in inp)
        noise=add(noise,mul(E,z,q),q)
        for k in (0,1):out[k]=add(out[k],mul(col[k],z,q),q)
    ph=add(out[1],mul(s,out[0],q),q,-1)
    assert ph==add(mul(low,P,q),noise,q)
    assert all((q//4<=c<3*q//4)==bool(v*x) for c,x in zip(ph,low))
# Every ideal rank terminal with 3 secret mask bits and two area columns.
for u,v,b in product(range(8),repeat=3):
  dot=lambda x,y:(x&y).bit_count()%2
  used={0,u,v,u^v}
  laws=[sorted((dot(a,u),dot(a,v),beta^dot(a,b)) for a in range(8)) for beta in (0,1)]
  assert (laws[0]==laws[1])==(b not in used)
print('270 full single-polynomial packets; 512 ideal rank views checked')
```

### sampler.py

```python
"""Outward-rounded bounds for a dyadic CDT with a fixed 220-coin cost."""
from decimal import Decimal as D, localcontext, ROUND_FLOOR, ROUND_CEILING
from hashlib import sha256
K=220
# 99 known decimal places enclose pi (Machin checks the bracket below).
from fractions import Fraction as F
def atan_bracket(x,t):
    s=sum(((-1)**j*x**(2*j+1)/(2*j+1) for j in range(t)),F())
    r=(-1)**t*x**(2*t+1)/(2*t+1)
    return min(s,s+r),max(s,s+r)
pi0=D('3.141592653589793238462643383279502884197169399375105820974944592307816406286208998628034825342117067')
with localcontext() as c:
    c.prec=160
    pi1=pi0+D('1e-99')
al,au=atan_bracket(F(1,5),90);bl,bu=atan_bracket(F(1,239),30)
assert F(pi0)<=16*al-4*bu<=16*au-4*bl<=F(pi1)
def table(s):
    with localcontext() as c:
        c.prec=140
        weights=[]
        for i in range(-200,201):
            c.rounding=ROUND_FLOOR;x=-pi1*(i*i)/(s*s);lo=x.exp().next_minus()
            c.rounding=ROUND_CEILING;x=-pi0*(i*i)/(s*s);hi=x.exp().next_plus()
            weights.append((lo,hi))
        c.rounding=ROUND_FLOOR;sl=sum(a for a,b in weights)
        c.rounding=ROUND_CEILING;su=sum(b for a,b in weights)
        pl=pu=D(0);rows=[]
        for lo,hi in weights[:-1]:
            c.rounding=ROUND_FLOOR;pl+=lo;v=pl*(2**K)/su
            c.rounding=ROUND_CEILING;pu+=hi;w=pu*(2**K)/sl
            assert w-v < D(1)/16
            rows.append(int(v))
        assert rows==sorted(rows)
        payload=b''.join(int(i).to_bytes(28,'big') for i in rows)
        print(s,len(rows),sha256(payload).hexdigest())
        return rows
if __name__=='__main__':
    for s in (9,24,30):table(s)
```

### Strength.lean

```lean
import SigabaNeoStd.Lattices.RingLWE
open SigabaNeo.Lattices
def par (n w m : ℕ) : RingLWE.Params := ⟨n,m,2^(w-1),.gauss 9,.uniform,Nat.pow_pos (by decide)⟩
#eval ([(1024,20,40960),(1024,26,53248),(1024,26,53),(1024,20,41),(2048,38,2560),(1024,26,14336)].map fun (n,w,m) => (n,w,m,RingLWE.H (par n w m)))
```
