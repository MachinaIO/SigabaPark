---
title: Exhaustive affine forgery comparison and full-size canonical join replay
refs: [note:pq-we-blinded-canonical-join]
tags: [witness-encryption, module-lwe, experiment]
---

Independent Python 3 listings, using only the standard library. The full generator hashes little-endian uint16 residues; this replay convention uses more bits than the proposed wire format. The output digest is df649d6a4a47cc30fed0e2679ecf3bd8fb30ecac2331b837ef0a291e8afbea0e.

### forgery.py

```python
"""Tiny exhaustive affine-ciphertext forgery model plus production integer bounds."""
from itertools import product
from fractions import Fraction
from math import log2
p=3
def add(a,b):return (a%3+b%3)%3+3*((a//3+b//3)%3)
def neg(a):return (-a%3)+3*(-(a//3)%3)
def mul(a,b):
 x,y=a%3,a//3;z,w=b%3,b//3
 return ((x*z-y*w)%3)+3*((x*w+y*z)%3)
all_maps=[[add(mul(x%3,c),mul(x//3,d)) for x in range(9)] for c,d in product(range(9),repeat=2)]
frob=[mul(mul(x,x),x) for x in range(9)]
assert frob in all_maps
samples=[(g,mul(g,frob[t]),mul(g,t)) for g,t in product(range(1,9),repeat=2)]
plain=sum(frob[frob[t]]==t for t in range(1,9))
framed=sum(frob[off]==target for g,off,target in samples)
homogeneous=0;affine=0
for a,b in product(all_maps,repeat=2):
 hist=[0]*9
 for g,off,t in samples:
  hist[add(t,neg(add(a[g],b[off])))] += 1
 homogeneous=max(homogeneous,hist[0])
 affine=max(affine,max(hist))
assert plain==8 and framed==16 and homogeneous<=24 and affine<=32
print('unframed Frobenius/8',plain,'same map after framing/64',framed)
print('max across 6561 homogeneous maps / 59049 affine rules; denominator64',homogeneous,affine)
Dmax=4*4224
for p,r,m in [(257,4,8),(769,4,6),(12289,12,1)]:
 Q=p**r
 bound=Fraction(Dmax+1,Q-1)**m
 print('strong affine-forgery lower bound in bits',p,r,m,-log2(float(bound)))

```

### packet.py

```python
"""Generate full CRT packet incrementally; retain only the blocks used in the replay."""
from random import Random
from hashlib import sha256
from math import gcd
rng=Random(176)
N=4224; M=2*N+1; n=128;k=8; m=4240
ps=[257,769];gens=[3,11];lanes=[8,6];r=4
def fm(a,b,p,u):
 v=[0]*7
 for i,x in enumerate(a):
  for j,y in enumerate(b):v[i+j]+=x*y
 return tuple((v[i]+(u*v[i+4] if i<3 else 0))%p for i in range(4))
one=(1,0,0,0);zero=(0,0,0,0)
def fpow(a,d,p,u):
 x=one
 while d:
  if d&1:x=fm(x,a,p,u)
  a=fm(a,a,p,u);d//=2
 return x
def uniform(p):
 while True:
  x=tuple(rng.randrange(p) for _ in range(4))
  if x!=zero:return x
def inverse(v,p,rho):
 v=v[:];j=0
 for i in range(1,n):
  b=n//2
  while j&b:j^=b;b//=2
  j^=b
  if i<j:v[i],v[j]=v[j],v[i]
 for h in (2,4,8,16,32,64,128):
  tw=[pow(rho,(-2*i*n//h)%(p-1),p) for i in range(h//2)]
  for start in range(0,n,h):
   for i,t in enumerate(tw):
    x=v[start+i];y=t*v[start+i+h//2]
    v[start+i]=(x+y)%p;v[start+i+h//2]=(x-y)%p
 return [x*norm[p][i]%p for i,x in enumerate(v)]
def idx(e,col):
 assert e!=M
 return (e-(e>M))*32+col
rho={p:pow(u,(p-1)//256,p) for p,u in zip(ps,gens)}
norm={p:[pow(n*pow(rho[p],j,p),-1,p) for j in range(n)] for p in ps}
I=19;J=3503
terms=[0,I,M-J,M+I-J]
needed={idx(e,c)//n for e in terms for c in range(32)}
records={}; sk={}; masks={}; secret={}; src={}
for p,u,L in zip(ps,gens,lanes):
 assert pow(u,(p-1)//2,p)!=1 and (p!=769 or pow(u,(p-1)//3,p)!=1)
 sk[p]=[[rng.randrange(p) for j in range(n)] for h in range(k)]
 ta=[uniform(p) for i in range(L)];g=[uniform(p) for i in range(L)]
 secret[p]=(ta,g)
 v=g[:]; stream=[]
 for e in range(4*N+1):
  if e!=M:
   stream.extend(x for val in v for x in val)
   stream += [0]*(32-4*L)
  v=[fm(x,y,p,u) for x,y in zip(v,ta)]
 masks[p]=stream
 src[p]={}
 for e in range(1,2*N+1):
  c=[tuple(rng.randrange(p) for i in range(r)) for l in range(L)]
  if e in (I,M-J):src[p][e]=c
digest=sha256()
for b in range(m):
 errs=[rng.getrandbits(1)-rng.getrandbits(1) for i in range(n)]
 for p in ps:
  A=[[rng.randrange(p) for z in range(n)] for t in range(k)]
  Y=inverse([sum(a*s for a,s in zip(v,w))%p for v,w in zip(zip(*A),zip(*sk[p]))],p,rho[p])
  for i in range(n):
   idx0=b*n+i;Y[i]=(Y[i]+errs[i]+(masks[p][idx0] if idx0<len(masks[p]) else 0))%p
  for row in A+[Y]:digest.update(b''.join(x.to_bytes(2,'little') for x in row))
  if b in needed:records[p,b]=A,Y,errs
for p,u,L in zip(ps,gens,lanes):
 ta,gs=secret[p]
 for l in range(L):
  c,d=src[p][I][l],src[p][M-J][l]
  a=tuple((x+y)%p for x,y in zip(c,fpow(ta[l],I,p,u)))
  b=tuple((x+y)%p for x,y in zip(d,fpow(ta[l],M-J,p,u)))
  target=fm(a,b,p,u); vals=[]
  for o in range(4):
   U=[[0]*n for h in range(k)];V=E=0
   for e,coef in zip(terms,[fm(c,d,p,u),d,c,one]):
    for j in range(4):
     weight=fm(coef,tuple(int(i==j) for i in range(4)),p,u)[o]
     if not weight:continue
     blk,slot=divmod(idx(e,4*l+j),n);A,Y,errors=records[p,blk]
     V+=weight*Y[slot];E+=weight*errors[slot];z=weight*norm[p][slot]%p;step=pow(rho[p],-2*slot,p)
     for i in range(n):
      for h in range(k):U[h][i]+=z*A[h][i]
      z=z*step%p
   vals.append((V-E-sum(a0*b0 for v,w in zip(U,sk[p]) for a0,b0 in zip(v,w)))%p)
   # Above uses only public opening weights plus fresh destination key.
  assert fm(tuple(vals),fpow(gs[l],p**4-2,p,u),p,u)==target
assert 16896*32==4224*n
print('4240 full rank-8 blocks, 14 quartic lanes, 56 normalized coordinates; digest of unpacked uint16 CRT records:',digest.hexdigest())

```

### h.lean

```lean
import SigabaNeoStd.Lattices.ModuleLWE
open SigabaNeo.Lattices
def main (args : List String) : IO Unit := do
  let k := args[0]!.toNat!
  let r := args[1]!.toNat!
  let m := ((16896*r+127)/128)+2*k
  let par : ModuleLWE.Params := ⟨128,k,m,197633,.cbd 1,.uniform,by decide⟩
  IO.println (k,r,m,ModuleLWE.H par)

```
Run the last listing in the pinned core with arguments 8 and 32. It prints (8, (32, (4240, 169))).
