---
title: Reproducible native indexed-issuer frames and equal-output tape transport
refs: [note:pq-we-indexed-native-frame]
tags: [witness-encryption, reproducibility]
---
Run the following standalone Python 3 file. Each test reconstitutes every coordinate, verifies all cross outputs, recovers the setup tape, and transports the same full transcript to a different admissible world. All 256 unary tapes are also enumerated in all 16 worlds. Numerical tests complement the universal frame and chart proofs.

```python
from random import Random
from itertools import product
from collections import Counter
from functools import reduce
from operator import xor
R=Random(162)
def low(n): return (1<<n)-1
def bit(x,i): return x>>i&1
class Grid:
    def __init__(self,a,b,c):
        self.a,self.b,self.c=a,b,c
        self.u=a+c-1;self.w=self.u*b;self.C=2*self.u+b+4*self.w
    def ez(self,z):
        a,c=self.a,self.c
        root=bit(z,0)
        return (low(a) if root else 0)|(((z>>1)^(low(c-1) if root else 0))<<a)
    def ew(self,grid,zrow):
        n=self.c if zrow else self.a
        return sum((self.ez((grid>>(j*n))&low(n)) if zrow else (grid>>(j*n))&low(n))<<(j*self.u) for j in range(self.b))
    def uv(self,u,v):
        return sum((u if bit(v,j) else 0)<<(j*self.u) for j in range(self.b))
    def ur(self,u,i,k):
        return bit(u,i)^(bit(u,self.a+k-1) if k else 0)
    def sample(self):
        u,w,b=self.u,self.w,self.b
        return tuple(R.getrandbits(n) for n in (1,u,u,b,w,w,w,w))
    def base(self,q,X,Y,Z):
        t,x0,x1,y,r0,r1,p0,p1=q;U=X^self.ez(Z);B=Y^y
        l=U if t else 0;r=U^l
        return (l^x0,r^x1,self.uv(l,y)^r0,self.uv(r,y)^r1,B,self.uv(x0,B)^r0^p0,self.uv(x1,B)^r1^p1)
    def offsets(self,q,raw,zrow):
        t=q[0];n=self.c if zrow else self.a
        l=raw if t else 0;r=raw^l
        mul=lambda f:sum((f if bit(q[3],j) else 0)<<(j*n) for j in range(self.b))
        return (l,r,mul(l),mul(r))
    def emb(self,s,zrow):
        u=self.ez if zrow else lambda z:z
        a,b,c,d=s;return (u(a),u(b),self.ew(c,zrow),self.ew(d,zrow),0,0,0)
    def masks(self,zrow):
        n=self.c if zrow else self.a
        return tuple(R.getrandbits(w) for w in [n,n,n*self.b,n*self.b])
    def packet(self,q,rx,rz,world):
        B,X,Y,Z=world;h=q[0]^B;key=(h,q[6+h])
        lx=tuple(map(xor,rx,self.offsets(q,X,False)));lz=tuple(map(xor,rz,self.offsets(q,Z,True)))
        ly=tuple(x^y^z for x,y,z in zip(self.base(q,0,Y,0),self.emb(rx,False),self.emb(rz,True)))
        return key,lx,ly,lz
    def recover(self,view,world):
        (h,ph),lx,ly,lz=view;B,X,Y,Z=world;t=h^B
        O=tuple(x^y^z for x,y,z in zip(self.emb(lx,False),ly,self.emb(lz,True)))
        U=X^self.ez(Z);l=U if t else 0;r=U^l
        y=Y^O[4]; x0=O[0]^l;x1=O[1]^r
        r0=O[2]^self.uv(l,y);r1=O[3]^self.uv(r,y)
        ps=[O[5]^self.uv(x0,O[4])^r0,O[6]^self.uv(x1,O[4])^r1]
        assert ps[h]==ph
        q=(t,x0,x1,y,r0,r1,*ps)
        rx=tuple(map(xor,lx,self.offsets(q,X,False)))
        rz=tuple(map(xor,lz,self.offsets(q,Z,True)))
        return q,rx,rz
    def test(self):
        a,b,c=self.a,self.b,self.c
        for attempt in range(200):
            B,X,Y,Z=(R.getrandbits(n) for n in (1,a,b,c))
            world=(B,X,Y,Z); q=self.sample();m=(q,self.masks(False),self.masks(True))
            V=self.packet(*m,world)
            assert self.recover(V,world)==m
            (h,ph),lx,ly,lz=V
            O=tuple(x^y^z for x,y,z in zip(self.emb(lx,False),ly,self.emb(lz,True)))
            assert O==self.base(q,X,Y,Z)
            out=self.uv(O[h],O[4])^O[2+h]^O[5+h]^ph
            assert out==(self.uv(X^self.ez(Z),Y) if B else 0)
            for i,j,k in product(range(a),range(b),range(c)):
                assert self.ur(out>>(j*self.u),i,k)==(B&(bit(X,i)^bit(Z,k))&bit(Y,j))
            alt=(B,X^low(a),Y,Z^low(c)) if out else R.choice([(0,R.getrandbits(a),R.getrandbits(b),R.getrandbits(c)),(1,low(a),R.getrandbits(b),low(c)),(1,R.getrandbits(a),0,R.getrandbits(c))])
            assert self.packet(*self.recover(V,alt),alt)==V
        S=2*(a+c)*(1+b)
        print((a,b,c),'u,w,C,S',self.u,self.w,self.C,S,'raw public',1+self.w+self.C+S,'eager',23*a*b*c)
for dims in [(1,1,1),(2,2,2),(3,4,5),(4,4,4),(8,4,8)]:Grid(*dims).test()
G=Grid(1,1,1);seen={}
for world in product(range(2),repeat=4):
    B,X,Y,Z=world;out=B&(X^Z)&Y;law=Counter()
    for q in product(range(2),repeat=8):law[(q[0]^B,q[6+(q[0]^B)],G.base(q,X,Y,Z))]+=1
    if out in seen:assert seen[out]==law
    else:seen[out]=law
print('Exact one-address multiplicity and 1000 full native tapes/alternate worlds passed.')
```
