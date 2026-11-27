---
title: Replay of full-size packed tag banks, CRT issuance, and registered strength calculations
refs: [note:pq-we-packed-tag-ring]
tags: [witness-encryption, ring-lwe, experiment]
---

The following independent Python 3 listings require only the standard library. Integer arithmetic, fixed PRNG seeds and host runtime are for reproducibility. They do not measure registry machine execution time.

### Dyadic one-gate replay

```python
"""Replay coefficient extraction and one-layer switching over power-of-two moduli."""

from random import Random
from itertools import product


def row(a, j):
    return [a[j-i] if i <= j else -a[j-i] for i in range(len(a))]


def convolution(a, s, q):
    out = [0] * len(a)
    for i, x in enumerate(a):
        for j, y in enumerate(s):
            h = i+j
            out[h % len(a)] += (1 if h < len(a) else -1) * x*y
    return [v % q for v in out]


def audit(qbits, digitbits):
    rng = Random(qbits)
    p, q = 1 << 160, 1 << qbits
    delta, mask = q//p, (1 << digitbits)-1
    tau = rng.randrange(p) | 1
    n, k = 5, 16
    tags = list(range(1,n+1)) + list(range(2*n,3*n))
    degrees = sorted(set(tags) | {u+v for u,v in product(tags,repeat=2) if u+v != 3*n})
    slot = [(d,j) for d in degrees for j in range(0,160,digitbits)]
    source = {u: (rng.randrange(p),rng.randrange(p)) for u in tags}
    s = [rng.randrange(-1,2) for _ in range(k)]
    bank = {}
    for start in range(0,len(slot),k):
        a = [rng.randrange(q) for _ in range(k)]
        bodies = convolution(a,s,q)
        for i,(d,j) in enumerate(slot[start:start+k]):
            b = (bodies[i]+rng.randrange(-8,9)+(delta<<j)*pow(tau,d,p)) % q
            bank[d,j] = row(a,i), b
    count = 0
    for u,v in product(tags,repeat=2):
        if u+v == 3*n:
            continue
        m,a = source[u]
        nlabel,b = source[v]
        c,d = (m-a*pow(tau,u,p))%p, (nlabel-b*pow(tau,v,p))%p
        out = delta*(c*d%p)
        header = [0]*k
        for degree, coefficient in [(u,a*d),(v,b*c),(u+v,a*b)]:
            for j in range(0,160,digitbits):
                digit = ((coefficient%p)>>j)&mask
                h, z = bank[degree,j]
                header = [x+digit*y for x,y in zip(header,h)]
                out += digit*z
        phase = (out-sum(x*y for x,y in zip(header,s)))%q
        assert ((phase+delta//2)//delta)%p == (m*nlabel)%p
        count += 1
    print(qbits, digitbits, count, "ordered legal products recovered")


if __name__ == "__main__":
    audit(208,32)
    audit(328,160)

```

### Composite small-q coefficient representation

```python
"""Full registered-size coefficient-slot experiment."""
from random import Random
from math import ceil, gcd
from collections import defaultdict
from time import monotonic
p=8191
d=12
n=2048
num_vars=4224
M=3*num_vars
D=6*num_vars-3
scale=2**33
q=p*scale
rng=Random(104168)
zero=(0,)*d
one=(1,)+(0,)*(d-1)
def add(x,y):
    return tuple((a+b)%p for a,b in zip(x,y))
def neg(x): return tuple((-a)%p for a in x)
def mul(x,y):
    z=[0]*(2*d-1)
    for i,a in enumerate(x):
        for j,b in enumerate(y): z[i+j]+=a*b
    for i in range(2*d-2,d-1,-1):
        z[i-d]-=12*z[i]; z[i-d+1]-=z[i]
    return tuple(a%p for a in z[:d])
def powf(a,e):
    result=one
    while e:
        if e&1: result=mul(result,a)
        a=mul(a,a);e//=2
    return result
def random_field(): return tuple(rng.randrange(p) for _ in range(d))
def basis(i): return tuple(int(i==j) for j in range(d))
def rem(a,b):
    a=list(a)
    while a and not a[-1]:a.pop()
    while len(a)>=len(b):
        c=a[-1]*pow(b[-1],-1,p)%p
        j=len(a)-len(b)
        for i,v in enumerate(b):a[i+j]=(a[i+j]-c*v)%p
        while a and not a[-1]:a.pop()
    return a
def gcdpoly(a,b):
    while b:a,b=b,rem(a,b)
    return a
X=basis(1)
for j in (4,6):
    u=add(powf(X,p**j),neg(X))
    assert len(gcdpoly([12,1]+[0]*10+[1],rem(u,[1]+[0]*12+[1])))==1
assert powf(X,p**12)==X
tau=random_field()
assert tau!=zero
ts=[one]
for i in range(1,6*num_vars-1): ts.append(mul(ts[-1],tau))
def offset(i,j):
    assert 1<=i<6*num_vars-1 and i!=M
    return (i-1-(i>M))*d+j
def kronecker(a,b):
    width=(2*q.bit_length()+n.bit_length()+7)//8
    def encode(v):return int.from_bytes(b''.join(c.to_bytes(width,'little') for c in v),'little')
    cv=(encode(a)*encode(b)).to_bytes(2*n*width,'little')
    def c(i):return int.from_bytes(cv[i*width:(i+1)*width],'little')
    return [(c(i)-c(n+i))%q for i in range(n)]
def signed_a(a,j,r):
    return a[j-r] if j>=r else -a[n+j-r]
def inner(x,y):return sum(a*b for a,b in zip(x,y))
sk=[rng.randrange(q) for _ in range(n)]
banks=[]
start=monotonic()
for i in range(ceil(D*d/n)+2):
    a=[rng.randrange(q) for _ in range(n)]
    y=kronecker(a,sk)
    j=rng.randrange(n)
    assert y[j]==sum(signed_a(a,j,r)*s for r,s in enumerate(sk))%q
    for j in range(n):
        index=i*n+j
        y[j]+=rng.getrandbits(1)-rng.getrandbits(1)
        if index<D*d:
            degree=(index//d)+1
            if degree>=M:degree+=1
            y[j]+=scale*ts[degree][index%d]
        y[j]%=q
    banks.append((a,y))
def trial(pos,negative):
    def source(support):
        f={};label=zero
        for i in support:
            m=random_field()
            f[i]=one
            label=add(label,m)
            f[0]=add(f.get(0,zero),add(m,neg(ts[i])))
        return f,label
    f,ml=source(pos);g,mr=source([M-i for i in negative])
    h={}
    for i,x in f.items():
        for j,y in g.items():h[i+j]=add(h.get(i+j,zero),mul(x,y))
    assert h.get(M,zero)==tuple([len(set(pos)&set(negative))]+[0]*11)
    if M in h: return
    overall=list(h.pop(0,zero))
    for i in range(d):
        U=[0]*n; V=overall[i]*scale
        for e,coef in h.items():
            for j in range(d):
                w=mul(coef,basis(j))[i]
                if not w:continue
                b,idx=divmod(offset(e,j),n)
                a,z=banks[b]; V+=w*z[idx]
                for r in range(n):U[r]+=w*signed_a(a,idx,r)
        phase=(V-inner(U,sk))%q
        overall[i]=((phase+scale//2)//scale)%p
    assert tuple(overall)==mul(ml,mr)
trial([2],[3])
trial([2,8,177,4000],[4,7,71])
trial([1,2,3],[2,3])
for a,y in banks[-2:]:
    z=kronecker(a,sk)
    assert all((x-t)%q in (0,1,q-1) for x,t in zip(y,z))
assert D*d*(p-1)==2490513480<scale//2
assert 2*len(banks)*n*q.bit_length()==28450816
print('validated',len(banks),'full RLWE blocks, 2048-dimensional hidden secret, 2 legal and 1 illegal aggregate; wall seconds',monotonic()-start)
print('power map image fibers',gcd(p**d-1,M),'field size',p**d)

```

### Exact-scale CRT transform-domain issuer and evaluator

```python
from math import ceil,gcd,isqrt
from random import Random
N=2048;NV=4224;M=3*NV;D=6*NV-3;r=12
p=12289; primes=(p,65537,114689);roots=(1331,54449,6932)
delta=primes[1]*primes[2];q=p*delta
rng=Random(171)
zero=(0,)*r;one=(1,)+(0,)*(r-1)
def fld():return tuple(rng.randrange(p) for _ in range(r))
def add(a,b):return tuple((u+v)%p for u,v in zip(a,b))
def sub(a,b):return tuple((u-v)%p for u,v in zip(a,b))
def mul(a,b):
 c=[0]*(2*r-1)
 for i,u in enumerate(a):
  for j,v in enumerate(b):c[i+j]+=u*v
 for i in range(2*r-2,r-1,-1):c[i-r]+=11*c[i]
 return tuple(u%p for u in c[:r])
def ntt(v,g,P):
 v=v[:]; j=0
 for i in range(1,N):
  bit=N>>1
  while j&bit:j^=bit;bit>>=1
  j^=bit
  if i<j:v[i],v[j]=v[j],v[i]
 h=2
 while h<=N:
  tw=[pow(g,j*(N//h),P) for j in range(h//2)]
  for k in range(0,N,h):
   for j,w in enumerate(tw):
    a=v[k+j];b=w*v[k+j+h//2]%P
    v[k+j]=(a+b)%P;v[k+j+h//2]=(a-b)%P
  h*=2
 return v
def inverse(v,g,P):
 w=ntt(v,pow(g,-2,P),P)
 return [a*pow(N*pow(g,i,P),-1,P)%P for i,a in enumerate(w)]
def coefs(i,j):return (i-1-(i>M))*r+j
def uniform_list(P):return [rng.randrange(P) for _ in range(N)]
tau=fld();ts=[one]
assert tau!=zero
for i in range(1,6*NV-1):ts.append(mul(ts[-1],tau))
for P,g in zip(primes,roots):
 assert all(P%i for i in range(2,isqrt(P)+1))
 assert pow(g,N,P)==P-1
assert all(pow(11,(p-1)//f,p)!=1 for f in (2,3))
assert 2*D*r*(p-1)<delta
ss=[uniform_list(P) for P in primes]
banks=[]
for b in range(ceil(D*r/N)+2):
 noises=[rng.getrandbits(1)-rng.getrandbits(1) for _ in range(N)]
 records=[]
 for P,g,sk in zip(primes,roots,ss):
  A=uniform_list(P)
  prod=[a*s%P for a,s in zip(A,sk)]
  Y=inverse(prod,g,P)
  # Independent evaluation of one inverse-NTT coefficient.
  j=(b*23+110)%N
  assert Y[j]==sum(v*pow(pow(g,2*h+1,P),-j,P) for h,v in enumerate(prod))*pow(N,-1,P)%P
  for j,e in enumerate(noises):
   idx=b*N+j;t=0
   if idx<D*r:
    d=idx//r+1;d+=int(d>=M);t=ts[d][idx%r]
   Y[j]=(Y[j]+e+delta*t)%P
  records.append((A,Y))
 banks.append(records)
I,J=17,3026
m1,m2=fld(),fld()
c,d=sub(m1,ts[I]),sub(m2,ts[M-J])
# Each degree contributes a scalar multiple to a chosen output coordinate.
terms=[(I,d),(M-J,c),(M+I-J,one)]
crt_one=[q//P*pow(q//P,-1,P) for P in primes]
recovered=[]
for k in range(r):
 residues=[]
 for pi,(P,g,sk) in enumerate(zip(primes,roots,ss)):
  U=[0]*N
  V=delta*mul(c,d)[k]
  for degree,h in terms:
   for j in range(r):
    basis=tuple(int(hh==j) for hh in range(r))
    w=mul(h,basis)[k]
    if not w:continue
    b,idx=divmod(coefs(degree,j),N)
    A,Y=banks[b][pi];V+=w*Y[idx]
    z=w*pow(N*pow(g,idx,P),-1,P)%P
    step=pow(g,-2*idx,P)
    for ii,a in enumerate(A):
     U[ii]+=z*a;z=z*step%P
  residues.append((V-sum(x*y for x,y in zip(U,sk)))%P)
 phase=sum(v*h for v,h in zip(residues,crt_one))%q
 recovered.append(((phase+delta//2)//delta)%p)
assert tuple(recovered)==mul(m1,m2)
print('151 complete CRT blocks, 453 independent coefficient checks and 12 FFT-domain output coordinates passed')
print('q,scale,aggregate error, CRT slots bit length',q,delta,D*r*(p-1),2*len(banks)*N*sum(x.bit_length() for x in primes))
count=len(banks)*N
kernel=lambda W:3*(2*W+3)+1
print('pointwise variable multiplier clock portion',sum(count*P.bit_length()*kernel(2*P.bit_length()) for P in primes))
print('schoolbook source scalar multiplier clock portion',(6*NV-2)*r*r*p.bit_length()*kernel(2*p.bit_length()))
print('dyadic source power multiplication clock portion',(6*NV-2)*160*kernel(160))
for n,w,b in [(8192,208,32),(8192,248,80),(8192,328,160)]:
 m=ceil(D*ceil(160/b)/n);print('dyadic',w,m,2*m*n*w+4*NV*160)

```

### Registry evaluation

Run this Lean file from the pinned core via lake env lean --run FILE n m q secret, passing decimal n,m,q and either cbd or uniform. Cases and outputs are given in the companion note.

```lean
import SigabaNeoStd.Lattices.RingLWE
open SigabaNeo.Lattices
def main (args : List String) : IO Unit := do
  let n := args[0]!.toNat!
  let m := args[1]!.toNat!
  let q := args[2]!.toNat!
  if h : 0 < q then
    let sd : SecretDist := if args[3]! == "cbd" then .cbd 1 else .uniform
    let par : RingLWE.Params := ⟨n,m,q,.cbd 1,sd,h⟩
    IO.println (RingLWE.H par)
```
