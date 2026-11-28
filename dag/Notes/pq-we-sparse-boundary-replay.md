---
title: Executable registered NAND replay for joint boundary projection
refs: [note:pq-we-sparse-boundary-projection]
tags: [witness-encryption, reproducibility]
---

Run the following self-contained Python 3 program. It reads only two freshly constructed registered NAND arrays in the parser phase. The assertions and exact size counters concern these examples. The degree and monotonicity arguments for arbitrary circuits are in the main note.

```python
from itertools import combinations, product
from random import Random
D=(3,7,25,36,37,43,52,57,59,71,77,92,97,105,106,109,110,117,119,121,124)
E=[(i,i^d) for i in range(128) for d in D if i<(i^d)]
R=[(i,j) for i,j in E if j<8]
anchor=next((i,j) for i,j in E if i>=8)
class C:
    def __init__(self,n):
        self.n=n;self.g=[]
    def N(self,a,b):
        self.g.append((a,b));return self.n+len(self.g)
    def neg(self,a):return self.N(a,a)
    def And(self,a,b):return self.neg(self.N(a,b))
    def Or(self,a,b):return self.N(self.neg(a),self.neg(b))
    def Xor(self,a,b):
        h=self.N(a,b);return self.N(self.N(a,h),self.N(b,h))
    def mux(self,y,f,h):return self.N(self.N(y,f),self.N(self.neg(y),h))
    def edge(self,idx,edges):
        t=[self.N(idx[i],idx[j]) for i,j in edges]
        v=t[0]
        for b in t[1:-1]:v=self.And(v,b)
        return self.N(v,t[-1]) if len(t)>1 else self.neg(v)
    def run(self,raw):
        z=[1]+list(raw)
        for a,b in self.g:z.append(1-z[a]*z[b])
        return z[-1]
    def pad(self,o):
        d=4096-len(self.g)
        if d%2:
            a=self.neg(o);one=self.N(o,a);o=self.N(a,one)
        while len(self.g)<4096:o=self.neg(self.neg(o))
        assert len(self.g)==4096
        live={self.n+4096}
        for j,(a,b) in reversed(list(enumerate(self.g,self.n+1))):
            assert j in live
            live.update((a,b))
def build(neg,raw):
    c=C(128 if raw else 8)
    w=list(range(1,c.n+1))
    if raw:w[8]=c.Xor(w[8],c.And(w[0],w[1]))
    def f():
        a=c.Xor(w[0],w[1]);b=c.Or(w[3],w[4])
        t=c.And(a,b)
        return c.And(t,c.neg(t)) if neg else t
    F=f()
    L=c.edge(w,R) if (neg or not raw) else None
    H=L if neg else c.And(c.Xor(w[2],w[5]),c.Or(c.neg(w[0]),w[7]))
    if raw:
        out=c.mux(c.edge(w,E),F,H);sz=len(c.g);c.pad(out)
    else:
        out=c.Or(F,c.And(c.neg(L),H));sz=len(c.g)
    return c,sz
def fv(x):return (x[0]^x[1])&(x[3]|x[4])
def hv(x):return (x[2]^x[5])&((1-x[0])|x[7])
def inv(x,q):
    old=list(x)+list(q)
    old[8]^=x[0]*x[1]
    return old
rng=Random(167)
for neg in (False,True):
    old,n=build(neg,True);new,g=build(neg,False)
    count=both=onlylo=onlyhi=0
    for x in product(range(2),repeat=8):
        l=any(x[i]*x[j] for i,j in R)
        e=fv(x) if not neg else 0
        h=hv(x) if not neg else l
        lo=[0]*120;hi=lo.copy()
        for j in anchor:hi[j-8]=1
        a,b=(old.run(inv(x,q)) for q in [lo,hi])
        assert new.run(x)==(a|b)==(e or (not l and h))
        both+=a and b;onlylo+=a and not b;onlyhi+=b and not a;count+=a|b
        if a or b:assert old.run(inv(x,hi if e else lo))
        q=[rng.randrange(2) for _ in range(120)]
        y=any((x+tuple(q))[i]*(x+tuple(q))[j] for i,j in E)
        assert old.run(inv(x,q))==(e if y else h)
    print("negative",neg,"live prepadding",n,"registered",len(old.g),"residual gates",g,"accepted retained",count,"endpoint totals",both,onlylo,onlyhi)
print("edge count",len(E),"retained",R,"anchor",anchor)
for _ in range(100):
    n=9;k=3
    E2=[rng.sample(list(combinations(range(n),2)),8) for _ in range(k)]
    for old in range(1<<n):
        wit=[{i,j} for edges in E2 for i,j in [next(((i,j) for i,j in edges if old>>i&old>>j&1),(-1,-1))] if i>=0]
        chosen=set().union(*wit) if wit else set()
        assert len(chosen)<=2*k
        assert all(any(old>>i&old>>j&1 for i,j in ed)==any(i in chosen and j in chosen for i,j in ed) for ed in E2)
print("51200 joint edge-profile checks")
for _ in range(160):
    n=12
    poly=[[tuple(rng.sample(range(n),rng.randrange(3))) for _ in range(5)] for j in range(2)]
    def y(x):return tuple(sum(all(x>>i&1 for i in t) for t in a)%2 for a in poly)
    q=rng.randrange(1<<n);tar=y(q)
    while q.bit_count()>4:
        chunk=[i for i in range(n) if q>>i&1][:5]
        q=next(q^sum(1<<chunk[j] for j in range(5) if m>>j&1) for m in range(1,32) if y(q^sum(1<<chunk[j] for j in range(5) if m>>j&1))==tar)
    assert y(q)==tar
print("160 two-output quadratic descent checks")

# Read only the registered NAND list to recover the boundary and rebuild the residual.
def resynth(original):
    n=128; gs=original.g
    def gate(i):
        assert n<i<=n+len(gs)
        return gs[i-n-1]
    def isneg(i):
        return i>n and gate(i)[0]==gate(i)[1]
    root=n+len(gs)
    while isneg(root) and isneg(gate(root)[0]):root=gate(gate(root)[0])[0]
    a,b=gate(root);y,f=gate(a);ny,h=gate(b)
    assert gate(ny)==(y,y)
    def edges(i):
        p,t=gate(i);vals=[t]
        while isneg(p):
            p,v=gate(gate(p)[0]);vals.append(v)
        vals.append(p)
        return [gate(v) for v in reversed(vals)]
    Y=edges(y)
    boundary=set(z for e in Y for z in e)
    derived=list(boundary-set(range(1,129)))
    assert len(derived)==1
    sh=derived[0]
    a,b=gate(sh); q,k=gate(a); k2,t=gate(b)
    # NAND XOR has outputs NAND(left,k), NAND(right,k).
    if k!=t:
        assert k==k2
        t=k2
    u,v=gate(k)
    assert u==q and q==9
    term=v
    assert gate(term)[0]==gate(term)[1] and gate(gate(term)[0])==(1,2)
    assert gate(a)==(q,k) and gate(b)==(term,k)
    assert q not in boundary
    idx={i:i-1 for i in range(1,129) if i!=q};idx[sh]=q-1
    E2=[(idx[u],idx[v]) for u,v in Y]
    assert all(0<=i<j<128 for i,j in E2)
    R2=[(i,j) for i,j in E2 if j<8]
    witness=next((i,j) for i,j in E2 if i>=8)
    child=C(8);memo={i:i for i in range(9)}
    def copy(i):
        if i in memo:return memo[i]
        if i<=128:raise ValueError("private wire leaks across interface")
        a,b=gate(i);memo[i]=child.N(copy(a),copy(b));return memo[i]
    F=copy(f); L=child.edge(list(range(1,9)),R2)
    same=False
    try:same=edges(h)==[(i+1,j+1) for i,j in R2]
    except AssertionError:pass
    H=L if same else copy(h)
    child.Or(F,child.And(child.neg(L),H))
    return child,len(E2),witness
for negative in (False,True):
    src,_=build(negative,True); verified,cnt,anchor2=resynth(src)
    expected,_=build(negative,False)
    assert all(verified.run(t)==expected.run(t) for t in product(range(2),repeat=8))
    print("parsed source, derived child:",negative,cnt,anchor2,len(verified.g))

def bits(c):return sum(4*a+2*b+3 for a,b in c.g)
for negative in (False,True):
    src,_=build(negative,True);nxt,_,_=resynth(src)
    print("exact statement encGates bits",negative,bits(src),bits(nxt))
es=[(i,i^t) for i in range(128) for t in D[:7] if i<i^t]
a,b=next((i,j) for i,j in es if i>=65)
big=C(128);F=C(64);w=list(range(1,129));p1=p2=1
for j in range(2500):
    p1=big.N(p1,1+j%64);p2=F.N(p2,1+j%64)
w[65]=big.Xor(w[65],big.And(w[0],w[1]))
y=big.edge(w,es)
o=big.And(p1,big.neg(big.Xor(y,w[64])))
sz=len(big.g);big.pad(o)
for _ in range(160):
    x=[rng.randrange(2) for i in range(64)]
    old=x+[1]+[0]*63
    old[a]=old[b]=1
    old[65]^=x[0]&x[1]
    assert big.run(old)==F.run(x)
print("arbitrary residual family representative",len(es),(a,b),sz,len(big.g),len(F.g),bits(big),bits(F))

```
