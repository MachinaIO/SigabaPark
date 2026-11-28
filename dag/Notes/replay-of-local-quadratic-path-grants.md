---
title: Replay of directed false graphs, characteristic-two cancellations and two-layer NAND residuals
refs: [definition:WE_CircuitSAT_Capped, note:joint-directed-path-residuals-and-local-readers, note:two-internal-layers-with-witness-local-polynomial-readout]
tags: [witness-encryption, reproducibility]
---

The following Python 3 enumeration compares entire transcripts in the two small unrestricted edge-mask examples and in both 4096-NAND modes of the polynomial construction. The path-count claim for all inputs of the latter follows from the two independent raw parity summaries.

```python
from itertools import product
from collections import Counter
from functools import reduce
def parity(v):return v.bit_count()%2
def poly_rem(a,b):
 while a and a.bit_length()>=b.bit_length():a^=b<<(a.bit_length()-b.bit_length())
 return a
def gcd(a,b):
 while b:a,b=b,poly_rem(a,b)
 return a
f=0x1100b;x=2
for i in range(1,17):
 x=poly_rem(sum(((x>>k)&1)<<(2*k) for k in range(16)),f)
 if i==8:assert gcd(x^2,f)==1
assert x==2
def raw(n,edges,b):
 h=Counter()
 for coins in range(1<<(n-1+len(edges))):
  R=[b]+[(coins>>i)&1 for i in range(n-1)]
  E=[(coins>>(n-1+i))&1 for i in range(len(edges))]
  D=[y^(flag&R[u]) for y,(u,v,flag) in zip(E,edges)]
  C=[R[v]^reduce(int.__xor__,[y for y,e in zip(E,edges) if e[1]==v],0) for v in range(1,n)]
  h[tuple(D+C+[R[-1]])]+=1
 return h
for n,es in [(6,[(0,1,1),(0,2,0),(1,3,1),(2,3,1),(2,4,1),(4,5,1),(3,5,0)]),(4,[(0,1,1),(0,2,1),(1,3,1),(2,3,1)])]:
 assert raw(n,es,0)==raw(n,es,1)
def circuit(d):
 G=[]
 def nand(a,b):G.append((a,b));return 128+len(G)
 def xor(a,b):
  t=nand(a,b);return nand(nand(a,t),nand(b,t))
 def fold(ix):return reduce(xor,ix)
 u=fold(range(1,65));v=fold(range(65,129));s=xor(u,v)
 ok=s if d else nand(s,s);ab=nand(u,v);ab=nand(ab,ab);last=nand(ab,ok)
 while len(G)<4095:nand(0,0)
 nand(last,last);return G
def ev(G,w):
 V=[1]+[(w>>i)&1 for i in range(128)]
 for x,y in G:V.append(1-V[x]*V[y])
 return V[-1]
for d in (0,1):
 G=circuit(d);assert len(G)==4096
 for w in [0,1,1<<64,(1<<64)+1,(1<<127)+4,(1<<128)-1]:
  u=parity(w%2**64);v=parity(w>>64)
  assert ev(G,w)==(u*v*(int((u^v)==d)))
 H=[]
 for bit in (0,1):
  hist=Counter()
  for A,B,C,h,g in product(range(2),repeat=5):
   z=(A,B^bit,C,d*h,h^((1^d)*g),h^A^C,g^B);hist[z]+=1
   if d==0:assert reduce(int.__xor__,z)==bit
  H.append(hist)
 print("mode",d,"support",len(H[0]),"shared",len(H[0].keys()&H[1].keys()))
 assert (H[0]==H[1])==bool(d)
print("directed-NO, cancelling diamond, extension field, and 4096-gate controls passed")
```
