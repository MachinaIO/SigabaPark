---
title: Reproducible read-once energy, frontier and terminal controls
refs: [note:pq-we-read-once-energy-endpoint]
tags: [witness-encryption, reproducibility]
---
Run each standalone Python 3 block under its heading. The first two scripts start from complete registered gate arrays, the third verifies the all-live interpolation and commutator controls, and the final one checks the growing-energy subcube.

### Read-once compiler

```python
"""Sparse one-pass energy evaluation for registered witnesses and claimed gate traces."""
from collections import defaultdict
from random import Random

P=16381
def compile_energy(gates):
    terms=defaultdict(int)
    def term(coefficient,*indices):
        terms[tuple(sorted(set(indices)-{0}))]+=coefficient
    for z,(a,b) in enumerate(gates,129):
        x=a if a<z else 0
        y=b if b<z else 0
        term(1,x,y)
        for v in (x,y):
            term(-2,v)
            term(2,v,z)
        term(3)
        term(-3,z)
    term(1)
    term(-1,128+len(gates))
    count=129+len(gates)
    slopes=[0]*count
    later=[[] for _ in range(count)]
    for indices,value in terms.items():
        if len(indices)==1: slopes[indices[0]]=value
        elif len(indices)==2 and value%P:
            i,j=indices
            later[i].append((j,value))
    return terms[()],slopes,later

def run(compiled,w):
    total,initial,later=compiled
    future=initial.copy()
    for i,x in enumerate(w,1):
        if x:
            total+=future[i]
            for j,coef in later[i]:
                future[j]+=coef
    return total%P
def direct(gates,w):
    vals=[1]+w
    total=1-vals[-1]
    for z,(a,b) in enumerate(gates,129):
        x=vals[a] if a<z else 1
        y=vals[b] if b<z else 1
        t=1-vals[z]
        total+=x*y-2*x*t-2*y*t+3*t
    return total
rng=Random(164)
maxedges=0
for k in range(8):
    gates=[]
    for z in range(129,4225):
        a=rng.choice([0,z,z+1,4224,rng.randrange(z)])
        b=rng.choice([0,a,z,4224,rng.randrange(z)])
        gates.append((min(a,4224),min(b,4224)))
    comp=compile_energy(gates)
    maxedges=max(maxedges,sum(map(len,comp[2])))
    for case in range(16):
        w=[rng.randrange(2) for _ in range(128)]
        for z,(a,b) in enumerate(gates,129):
            x=w[a-1] if 0<a<z else 1
            y=w[b-1] if 0<b<z else 1
            w.append(1-x*y if case==0 else rng.randrange(2))
        assert run(comp,w)==direct(gates,w)
        if case==0: assert run(comp,w)==1-w[-1]
print('128 full registered traces checked, 4224 single-bit choices per run, maximum nonzero pair coefficients among control circuits:',maxedges)
```

### Parity orders

```python
"""Compare two read-once orders for the same all-live 4096-gate parity trace."""
from collections import Counter
from random import Random
gates=[]
def nand(a,b):
    gates.append((a,b))
    return 128+len(gates)
not_bits=[nand(i,i) for i in range(1,129)]
optimal=[1,not_bits[0]]
acc=not_bits[0]
for i in range(1,128):
    b=not_bits[i]
    t=nand(acc,b)
    a1=nand(acc,t)
    b1=nand(b,t)
    acc=nand(a1,b1)
    optimal.extend([i+1,b,t,a1,b1,acc])
while len(gates)<4096:
    acc=nand(acc,acc)
    optimal.append(acc)
assert sorted(optimal)==list(range(1,4225))
live={4224}
for i,(a,b) in reversed(list(enumerate(gates,129))):
    assert i in live
    live.update((a,b))

def compile_frontiers(order):
    pos={var:i for i,var in enumerate(order)}
    uses={var:pos[var] for var in order}
    checks=[[] for _ in order]
    for z,(x,y) in enumerate(gates,129):
        j=max(pos[v] for v in (x,y,z))
        checks[j].append((x,y,z))
        for v in (x,y,z):uses[v]=max(uses[v],j)
    prev=()
    for i,var in enumerate(order):
        now=tuple(v for v in (*prev,var) if uses[v]>i)
        yield var,prev,checks[i],now
        prev=now
def run(order):
    states={()}
    peak=0
    total=0
    for v,prev,checks,now in compile_frontiers(order):
        next_states=set()
        for state in states:
            for bit in (0,1):
                x=dict(zip(prev,state))
                x[v]=bit
                if v==4224 and bit==0:continue
                if all(x[z]==1-x[a]*x[b] for a,b,z in checks):
                    next_states.add(tuple(x[a] for a in now))
        states=next_states
        peak=max(peak,len(states))
        total+=len(states)
    assert states=={()}
    return peak,total
rng=Random(165)
for _ in range(200):
    w=rng.getrandbits(128)
    values=[1]+[w>>i&1 for i in range(128)]
    for a,b in gates: values.append(1-values[a]*values[b])
    assert values[-1]==w.bit_count()%2
    assert values[129:257]==[1-b for b in values[1:129]]
print('accepted witness-first inequivalent prefixes = 2^127; all gates live')
print('interleaved live-bit peak',max(len(f[-1]) for f in compile_frontiers(optimal)))
print('interleaved reachable nonrejecting states: peak and sum',run(optimal))
```

### Terminal controls

```python
from random import Random
from collections import defaultdict
from itertools import product
from math import prod
P=16381
assert all(P%i for i in range(2,128))
def fixture():
    g=[(1,2)]
    while len(g)<4093:
        u=128+len(g);g.append((u,u))
    u=128+len(g);g.extend([(u,u),(u,u+1),(u+2,u+2)])
    live={4224}
    for i,(x,y) in reversed(list(enumerate(g,129))):
        assert i in live;live.update((x,y))
    return g
def energy(g,x):
    a=[1]+x
    return 1-a[-1]+sum((a[i] if i<z else 1)*(a[j] if j<z else 1)
        -2*((a[i] if i<z else 1)+(a[j] if j<z else 1))*(1-a[z])+3*(1-a[z]) for z,(i,j) in enumerate(g,129))
g=fixture();x0=[0]*4224;x1=x0.copy();x1[0]=1
e0,e1=energy(g,x0),energy(g,x1);assert (e0,e1)==(12289,12287)
t=e0*pow(e0-e1,-1,P)%P;assert t==14335 and ((1-t)*e0+t*e1)%P==0
# One column minor independent of the self-pair diagonals in a commuting completion.
def mixed(i,j):
    S=[0]*4224;S[i-1]=S[j-1]=1
    a=energy(g,S);S[i-1]=0;b=energy(g,S);S[i-1]=1;S[j-1]=0
    return a-b-energy(g,S)+e0
assert [mixed(i,j) for i in (1,130) for j in (2,131)]==[1,0,0,4]
# A two-dimensional Heisenberg factor suffices for the tested first two generators.
def add(a,b):return tuple((x+y)%P for x,y in zip(a,b))
def neg(a):return tuple(-x%P for x in a)
def dot(a,b):return sum(x*y for x,y in zip(a,b))%P
def mul(x,y):return (add(x[0],y[0]),add(x[1],y[1]),(x[2]+y[2]+dot(x[0],y[1]))%P)
def inv(x):return (neg(x[0]),neg(x[1]),(dot(x[0],x[1])-x[2])%P)
def word(*xs):
    out=((0,0),(0,0),0)
    for x in xs:out=mul(out,x)
    return out
def power(x,n):
    a=word()
    while n:
        if n&1:a=mul(a,x)
        x=mul(x,x);n>>=1
    return a
def random(r):return ((r.randrange(P),r.randrange(P)),(r.randrange(P),r.randrange(P)),r.randrange(P))
G=[((1,0),(0,0),-2),((0,1),(1,0),-2)]
rng=Random(165);origin=((0,0),(0,0),e0)
for _ in range(100):
    masks=[random(rng) for i in range(4)]
    z=[word(inv(masks[i]),masks[i+1]) for i in range(2)]
    p=word();D=[]
    for i in range(2):
        one=word(inv(masks[i]),G[i],masks[i+1]);D.append(word(p,one,inv(z[i]),inv(p)));p=mul(p,z[i])
    C=word(D[0],D[1],inv(D[0]),inv(D[1]))
    tail=word(inv(masks[2]),masks[3])
    forged=word(origin,masks[0],power(C,P-e0),p,tail,inv(masks[3]))
    assert forged==word()
    # Unknown affine frame over vector coordinates: two legal paths suffice.
    a=[rng.randrange(P) for i in range(4)];v=[rng.randrange(P) for i in range(3)]
    s0=(e0+a[0]+dot(tuple(a[1:]),tuple(v)))%P
    v1=[rng.randrange(P) for i in range(3)]
    s1=(e1+a[0]+dot(tuple(a[1:]),tuple(v1)))%P
    vf=[((1-t)*x+t*y)%P for x,y in zip(v,v1)]
    assert ((1-t)*s0+t*s1-a[0]-dot(tuple(a[1:]),tuple(vf)))%P==0
print('all-live NO and 100 random endpoint gauges;',e0,e1,'interpolation scalar',t,'commutator exponent',P-e0)
n=4224;m=4096;edges=3*m
print('sparse bits',40*edges+14*(n+1),'dense one-branch bits',14*n*(2*n+1),'dense both branches',28*n*(2*n+1),'unary input upper bound',m*(6*4224+3))
```

### Independent energy coordinates

```python
"""All-live registered NO circuit and a restricted cube of its integer energies."""
from math import comb
from random import Random
from itertools import product

modulus = 16381
assert all(modulus % k for k in range(2, 128))
gates = []
def nand(x, y):
    gates.append((x, y))
    return 128 + len(gates)
u = 0
for _ in range(4093):
    u = nand(u, 1)
nu = nand(u, u)
one = nand(u, nu)
nand(one, one)
assert len(gates) == 4096
live = {4224}
for gate, (x, y) in reversed(list(enumerate(gates, 129))):
    if gate in live:
        live.update((x,y))
assert set(range(129,4225)) <= live

def energy(flips):
    wires = [1] + [0]*128
    score = 0
    for j,(a,b) in enumerate(gates,1):
        x,y = wires[a],wires[b]
        z = (1-x*y) ^ (j in flips)
        t = 1-z
        score += x*y-2*x*t-2*y*t+3*t
        wires.append(z)
    return score + 1-wires[-1]

indices=list(range(2,4093,2))
rng=Random(163)
for k in [0,1,2,12,1024,len(indices)]:
    assert energy(set(rng.sample(indices,k))) == 1+k
n=len(indices)
difference=sum((-1)**(n-k)*comb(n,k)*pow(k+1,-1,modulus) for k in range(n+1))%modulus
assert difference==((-1)**n*pow(n+1,-1,modulus))%modulus!=0
print('live gates',len(gates),'independent coordinates',n,'highest multilinear coefficient mod',modulus,':',difference)
```
