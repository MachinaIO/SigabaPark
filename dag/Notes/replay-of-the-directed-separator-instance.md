---
title: Replaying the fixed 2048-coefficient source and the 4096-NAND quotient instance
refs: [definition:WE_CircuitSAT_Capped, note:quotient-separators-and-compact-monotone-joins]
tags: [witness-encryption, reproducibility]
---

This deterministic Python 3 test uses pseudorandom fixtures for reproducibility. The mathematical sampler uses fresh independent fair bits. The packed integer multiplication performs an ordinary convolution with sufficient digits to prevent carries between coefficients, followed by signed negacyclic folding and reduction modulo 64. Sparse independent direct checks validate this optimized replay. Each fixture runs 24 raw assignments per payload across all eight summary triples, including different representatives; six of those assignments are true in the first fixture and zero in the second. The truth of the remaining assignments follows from the OR quotient proof.

```python
"""Replay of six root grants for two overlapping 88-bit separators."""
from itertools import product
from random import Random
from collections import defaultdict, Counter
rng=Random(753149)
N=2048
bits=6*N
def packcs(words):
 return sum(w<<(6*i) for i,w in enumerate(words))
def mult(a,x):
 n=len(a); width=(n*63*63).bit_length()
 base=1<<width; mask=base-1
 f=sum(c<<(width*i) for i,c in enumerate(a))
 g=sum((c%64)<<(width*i) for i,c in enumerate(x))
 z=f*g
 return [(((z>>(width*i))&mask)-((z>>(width*(i+n)))&mask))%64 for i in range(n)]
def cbd(seed):
 n=N
 a=[((seed>>(2*i))&1)-((seed>>(2*i+1))&1) for i in range(3*n)]
 return a[:n],a[n:2*n],a[2*n:]
def expand(A,seed):
 s,*ee=cbd(seed)
 return [packcs([(x+y)%64 for x,y in zip(mult(a,s),e)]) for a,e in zip(A,ee)]
aa=[rng.randrange(64) for _ in range(N)];xx=[rng.randrange(-1,2) for _ in range(N)]
yy=mult(aa,xx)
for i in range(0,N,73):
 assert yy[i]==sum(aa[j]*xx[(i-j)%N]*(1 if j<=i else -1) for j in range(N))%64
A=[[rng.randrange(64) for _ in range(N)] for _ in range(2)]
two=list(product(range(2),repeat=2))
three=list(product(range(2),repeat=3))
def build(yes):
 gs=[]
 def nand(a,b):
  gs.append((a,b)); return 128+len(gs)
 def NOT(a):return nand(a,a)
 def AND(a,b):return NOT(nand(a,b))
 def OR(a,b):return nand(NOT(a),NOT(b))
 def XOR(a,b):
  h=nand(a,b);return nand(nand(a,h),nand(b,h))
 def group(seq):
  x=seq[0]
  for y in seq[1:]:x=OR(x,y)
  return x
 a,b,c=(group(seq) for seq in (list(range(1,41)),list(range(41,89)),list(range(89,129))))
 l=XOR(a,b); r=XOR(b,c)
 root=nand(a,NOT(c)) if yes else OR(XOR(a,c),AND(NOT(l),NOT(r)))
 v=NOT(AND(AND(l,r),root))
 while len(gs)<4095:nand(0,0)
 nand(v,v);return gs
def value(gs,w):
 vals=[1]+list(w)
 for a,b in gs:vals.append(1-vals[a]*vals[b])
 return vals[-1]
def root_ok(yes,a,b,c):
 return (a<=c) if yes else (a!=c or a==b==c)
def issue(yes,bit):
 gs=build(yes);rows=[q for q in three if root_ok(yes,*q)]
 r0=rng.getrandbits(bits)
 leaves={(side,p):rng.getrandbits(bits) for side in range(2) for p in two}
 refs=defaultdict(list)
 for row in rows:
  refs[0,row[:2]].append(row);refs[1,row[1:]].append(row)
 pads={};expanded=0
 for label,uses in refs.items():
  keys=[leaves[label]] if len(uses)==1 else expand(A,leaves[label])
  assert len(uses)==len(keys)
  expanded+=len(uses)-1
  for row,k in zip(uses,keys):pads[row,label]=k
 grants={row:r0^pads[row,(0,row[:2])]^pads[row,(1,row[1:])] for row in rows}
 leafpub={key:k for key,k in leaves.items() if key[1][0]!=key[1][1]}
 assert len(gs)==4096 and len(grants)==6 and len(leafpub)==4 and expanded==4
 cases=hits=0
 for row in three:
  a,b,c=row
  for rep in (0,1,2):
   w=[]
   for v,n in ((a,40),(b,48),(c,40)):
    w.extend([0 if not v else int(i==rep or rep==2 and i%2==0) for i in range(n)])
   expect=value(gs,w);state=int(row in grants and (0,row[:2]) in leafpub and (1,row[1:]) in leafpub)
   assert state==expect
   if state:
    val=grants[row];decsplit=0
    for label in ((0,row[:2]),(1,row[1:])):
     uses=refs[label];key=leafpub[label]
     out=[key] if len(uses)==1 else expand(A,key)
     decsplit+=len(uses)-1
     val^=out[uses.index(row)]
    assert val==r0 and (((bit^(r0&1))^(val&1))==bit)
    assert decsplit==1
   cases+=1;hits+=state
 return cases,hits
for yes in (False,True):
 print(yes,[(b,issue(yes,b)) for b in range(2)])
print("4096 gates, 128 inputs, 10 grant strings, 4 source calls, 147457 published bits")
```
