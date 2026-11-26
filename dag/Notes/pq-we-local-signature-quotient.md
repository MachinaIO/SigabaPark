---
title: Quotienting local NAND subcircuits by their exported wire patterns
refs: [definition:WE_CircuitSAT, note:we-circuitsat-live-wire-baseline]
tags: [circuit-sat, witness-encryption, baseline]
---

A verifier may expose no pairwise constraints on accepting inputs yet use each group of input bits only through a handful of intermediate values. This note gives an executable, assumption-free one-bit WE construction for the registered NAND format, a compressed verification relation for split-witness ABE, and a control separating this optimization from every sound pair filter on original inputs. The Boolean synthesis idea is related to [functional decomposition](https://people.eecs.berkeley.edu/~alanmi/research/dec/decClassify.htm). We quotient by observable intermediate values; their number can exceed the minimum quotient of the final Boolean function.

Partition the n original inputs into disjoint blocks of at most k bits. Normalize every read of an unavailable wire to constant true at that gate. Propagate syntactic block ownership from inputs, treating constant-only wires as usable everywhere. A gate belongs to a block when its nonconstant operands all belong to the same block; all other nonconstant gates are global. Retain the output cone, and for each block collect the local wires read by global gates plus the circuit output if local. Tabulate this vector over each local assignment and deduplicate it. Give each distinct vector an index and retain one realizing assignment. A block with no visible wires has just one class. Constant-only and empty circuits are handled by the same construction. An optional second partition greedily joins the input sets of gate operands while the block-size bound permits, renumbers inputs, and repeats the exact algorithm. Partition quality affects cost only.

**Exactness and encryption.** Induction on the original gate order shows every tabulated local wire equals its original value, and every global gate on the selected signature tuple equals the original gate on the input. Conversely any tuple of valid indices is realized by concatenating the stored representatives, since the blocks are disjoint. Thus unrestricted Cartesian enumeration introduces no infeasible witnesses and the full output Boolean function factors through the quotient. A satisfying witness can be encoded by lookup, and a satisfying code lifts to a satisfying representative. Lossless recovery of the original witness need not hold. Let M be the product of the class counts. Pack all M residual outputs in a bit vector: mixed-radix digit patterns repeat with stride equal to the product of preceding radices. Run each remaining NAND once on these bit planes. Encrypt b as b AND (the output plane is nonzero), and decrypt by returning the bit. This proves perfect correctness and identical ciphertexts on false statements, including against quantum distinguishers. If both tested partitions exceed the cap use the original exhaustive algorithm. In a split-ABE route the policy instead verifies one tuple and rejects out-of-range indices; conversion introduces no additional hardness premise. A full lattice instantiation, Lean proof of the compiler and registered machine clock are open.

For fixed k the public local tables have at most 2^k rows per wire; writing and grouping export vectors costs work proportional to their lengths per local row, plus dictionary or sorting costs. The direct packed evaluation uses O((s+1) ceiling(M/W)) words including intermediates at W-bit word width, plus local tables, and O(r ceiling(M/W)) word operations for r global NANDs once their input planes are ready. Constructing planes, parsing unary wire indices, selecting a partition and preprocessing carry additional costs. The Python bit-extraction loops and big-integer shifts have their own overhead. At k=8, cap=65536 the dense residual plane is at most 8 KiB per wire. A failed attempt adds preprocessing to the worst-case exhaustive cost; no universal improvement of the registered time bound follows.

**Controls.** The 128-input, 4,096-gate lists compute 16 eight-bit parities and then a predicate of these parities. One predicate is a cycle of 16 inequalities. Replacing one inequality by equality produces the inconsistent control. A second predicate is a seeded 68-clause three-literal CNF. Replacing its first eight clauses to exclude all eight assignments on three variables produces its inconsistent control. A direct source-CNF scan independently checks the number of accepting signatures. On any satisfiable control, *every* partial raw assignment fixing at most seven bits can be extended: choose a satisfying parity tuple, then set a remaining bit in each block to obtain that parity. Therefore no sound original-input pair filter can remove even one possible pair tuple. These constructed families evaluate the benefit on modular circuits; the 16-bit source relation itself already has a 16-bit witness.

| Residual predicate | Global NANDs | Accepting signatures / 65,536 |
|---|---:|---:|
| Even inequality cycle | 94 | 2 |
| Cycle with one equality | 95 | 0 |
| Planted nonlinear CNF | 338 | 24 |
| Inconsistent nonlinear CNF | 338 | 0 |

The local table step for the cycle took around 3.4 ms (median of five local Python runs). Scalar exhaustive residual evaluation was around 0.51 s; packed residual evaluation was below 0.5 ms in the recorded median runs. A complete fixed-partition quotient build and packed check of the nonlinear controls took around 8–10 ms in a single local run each, excluding circuit construction and unary parsing. Timing varies. Every circuit contains padding; the global NAND counts include only output-reachable gates after local compilation. For split ABE, a 16-bit tuple uses two tables of 256 items each, compared with two tables of 2^64 on the raw inputs. Here the measured direct decision path already avoids ABE. With the cycle inputs transposed across the supplied eight-bit blocks, the first partition gives M=2^128 and its dense allocation is skipped. The gate-based permutation recovers M=65,536. There is no guarantee it finds an optimal partition.

**Reproduction.** Below is standalone Python 3, including the complete bit encryption entry point. It exhausts the 625 two-input two-gate circuits at two block widths, checks 400 additional random circuits, compares all packed output positions on another 400 small circuits, and checks capped encryption with a fallback. The exhaustive baseline is intended for small fallback tests; it can cost 2^128 evaluations at the registered size.

~~~python
from itertools import product
from math import prod
from random import Random
from statistics import median
from time import perf_counter

def evaluate(n,g,x):
    w=[1]+[(x>>i)&1 for i in range(n)]
    for a,b in g:
        w.append(1-((w[a] if a<len(w) else 1)&(w[b] if b<len(w) else 1)))
    return w[-1] if g else 1

class Quotient:
    def __init__(self,n,g,k):
        # -1 marks constants and -2 marks global gates in the owner table.
        blocks=(n+k-1)//k
        owners=[-1]+[i//k for i in range(n)]
        edges={}
        for a,b in g:
            v=len(owners)
            a=a if a<v else 0
            b=b if b<v else 0
            edges[v]=a,b
            p,q=owners[a],owners[b]
            owners.append(q if p==-1 else p if q==-1 or p==q else -2)
        self.out=len(owners)-1 if g else 0
        live={self.out}
        for v in reversed(edges):
            if v in live:live.update(edges[v])
        outputs=[set() for _ in range(blocks)]
        global_gates=[]
        for v,(a,b) in edges.items():
            if v in live and owners[v]==-2:
                global_gates.append((v,a,b))
                for w in (a,b):
                    if owners[w]>=0:outputs[owners[w]].add(w)
        if owners[self.out]>=0:outputs[owners[self.out]].add(self.out)
        self.gates=global_gates
        self.constants={0:1}
        tables={}
        for j in range(blocks):
            width=min(k,n-j*k)
            size=1<<width
            for h in range(width):
                v=1+j*k+h
                if v in live:tables[v]=sum(((x>>h)&1)<<x for x in range(size))
        for v,(a,b) in edges.items():
            j=owners[v]
            if v not in live or j==-2:continue
            if j==-1:
                self.constants[v]=1-(self.constants[a]&self.constants[b])
                continue
            mask=(1<<(1<<min(k,n-j*k)))-1
            def word(w):
                if w in self.constants:return mask*self.constants[w]
                return tables[w]
            tables[v]=mask^(word(a)&word(b))
        self.parts=[]
        for j,outs in enumerate(outputs):
            outs=sorted(outs)
            size=1<<min(k,n-j*k)
            seen={}
            sigs=[]
            ids=[]
            reps=[]
            for x in range(size):
                pattern=tuple(tables[v]>>x&1 for v in outs)
                if pattern not in seen:
                    seen[pattern]=len(sigs)
                    sigs.append(pattern)
                    reps.append(x)
                ids.append(seen[pattern])
            self.parts.append((j*k,size,outs,sigs,ids,reps))
        self.count=prod(len(p[3]) for p in self.parts)

    def encode(self,x):
        return tuple(ids[(x>>shift)%size] for shift,size,_,_,ids,_ in self.parts)
    def lift(self,z):
        return sum(p[5][i]<<p[0] for p,i in zip(self.parts,z,strict=True))
    def residual(self,z):
        w=dict(self.constants)
        for p,i in zip(self.parts,z,strict=True):
            w.update(zip(p[2],p[3][i]))
        for v,a,b in self.gates:w[v]=1-(w[a]&w[b])
        return w[self.out]

def tiny(n,g,k):
    q=Quotient(n,g,k)
    words=set()
    for x in range(1<<n):
        z=q.encode(x)
        words.add(z)
        assert evaluate(n,g,x)==q.residual(z)==evaluate(n,g,q.lift(z))
    assert len(words)==q.count

for a,b,c,d in product(range(5),repeat=4):
    for k in (1,2):tiny(2,[(a,b),(c,d)],k)
r=Random(8001)
for _ in range(400):
    n=r.randrange(9);s=r.randrange(15)
    tiny(n,[(r.randrange(n+s+1),r.randrange(n+s+1)) for _ in range(s)],r.randint(1,5))

def control(order,unsat):
    g=[]
    def nand(a,b):
        g.append((a,b))
        return 128+len(g)
    def xor(a,b):
        t=nand(a,b)
        return nand(nand(a,t),nand(b,t))
    def parity(ws):
        v=ws[0]
        for w in ws[1:]:v=xor(v,w)
        return v
    z=[parity(order[i:i+8]) for i in range(0,128,8)]
    clauses=[xor(z[i-1],z[i]) for i in range(16)]
    if unsat:clauses[-1]=nand(clauses[-1],clauses[-1])
    while len(g)<4096-2*(len(clauses)-1):nand(0,0)
    v=clauses[0]
    for w in clauses[1:]:
        t=nand(v,w)
        v=nand(t,t)
    return g

for name,order,unsat in [('aligned SAT',list(range(1,129)),False),
                         ('aligned UNSAT',list(range(1,129)),True),
                         ('transposed SAT',[1+i+16*j for i in range(16) for j in range(8)],False)]:
    g=control(order,unsat)
    prep=[]
    for _ in range(5):
        start=perf_counter()
        q=Quotient(128,g,8)
        prep.append(perf_counter()-start)
    for _ in range(100):
        x=r.getrandbits(128);z=q.encode(x)
        assert q.residual(z)==evaluate(128,g,x)==evaluate(128,g,q.lift(z))
    ans='skipped';elapsed=0
    if q.count<=65536:
        start=perf_counter()
        ans=sum(q.residual(z) for z in product(*(range(len(p[3])) for p in q.parts)))
        elapsed=perf_counter()-start
        assert ans==(0 if unsat else 2)
    print(name,q.count,len(q.gates),ans,round(1000*median(prep),2),round(elapsed,3))

def infer_order(n,g,k):
    # Merge the two locally owned components of a gate when their union fits.
    parent=list(range(n))
    weight=[1]*n
    def root(i):
        while parent[i]!=i:
            parent[i]=parent[parent[i]]
            i=parent[i]
        return i
    wires=[-1]+list(range(n))
    for a,b in g:
        v=len(wires)
        a=wires[a] if a<v else -1
        b=wires[b] if b<v else -1
        if a==-2 or b==-2:h=-2
        elif a==-1:h=b
        elif b==-1:h=a
        else:
            a,b=root(a),root(b)
            if a==b:h=a
            elif weight[a]+weight[b]>k:h=-2
            else:
                if weight[a]<weight[b]:a,b=b,a
                parent[b]=a
                weight[a]+=weight[b]
                h=a
        wires.append(h)
    groups={}
    for i in range(n):groups.setdefault(root(i),[]).append(i+1)
    # Fixed-size blocks in the reference: concatenation may split small components.
    order=[v for vs in groups.values() for v in vs]
    index={w:i+1 for i,w in enumerate(order)}
    return order,[(index.get(a,a),index.get(b,b)) for a,b in g]

order,g2=infer_order(128,g,8)
q2=Quotient(128,g2,8)
assert q2.count==65536 and len(q2.gates)==len(Quotient(128,control(list(range(1,129)),False),8).gates)
for _ in range(400):
    x=r.getrandbits(128)
    permuted=sum((x>>(v-1)&1)<<i for i,v in enumerate(order))
    assert evaluate(128,g,x)==q2.residual(q2.encode(permuted))
print('transposed after inferred order',q2.count,len(q2.gates))

def repeat_word(word,width,copies):
    result=0
    offset=0
    while copies:
        if copies&1:
            result |= word<<offset
            offset+=width
        copies >>= 1
        if copies:
            word |= word<<width
            width*=2
    return result

def packed(q,cap):
    m=q.count
    if m>cap:return None
    ones=(1<<m)-1
    w={v:b*ones for v,b in q.constants.items()}
    stride=1
    for _,_,outs,sigs,_,_ in q.parts:
        period=stride*len(sigs)
        for j,v in enumerate(outs):
            pat=sum(((1<<stride)-1)<<(i*stride) for i,t in enumerate(sigs) if t[j])
            w[v]=repeat_word(pat,period,m//period)
        stride=period
    for v,a,b in q.gates:w[v]=ones^(w[a]&w[b])
    return w[q.out]

for unsat in (False,True):
    g=control(list(range(1,129)),unsat)
    q=Quotient(128,g,8)
    ts=[]
    for _ in range(11):
        start=perf_counter(); mask=packed(q,65536)
        ts.append(perf_counter()-start)
    assert mask.bit_count()==(0 if unsat else 2)
    print('packed UNSAT' if unsat else 'packed SAT',round(1000*median(ts),3),'ms')
for _ in range(400):
    n=r.randrange(9);s=r.randrange(15)
    g=[(r.randrange(n+s+1),r.randrange(n+s+1)) for _ in range(s)]
    q=Quotient(n,g,r.randint(1,4))
    mask=packed(q,256)
    for j in range(q.count):
        i=j;z=[]
        for p in q.parts:
            i,t=divmod(i,len(p[3]))
            z.append(t)
        assert mask>>j&1==q.residual(z)

def nonlinear(unsat):
    # Same parity encoders; a seeded nonmonotone CNF is the residual computation.
    rr=Random(81)
    g=control(list(range(1,129)),False)[:16*7*4]
    z=[128+28*(i+1) for i in range(16)]
    def nand(a,b):
        g.append((a,b))
        return 128+len(g)
    planted=rr.getrandbits(16)
    clauses=[]
    for _ in range(68):
        vs=rr.sample(range(16),3)
        signs=[rr.randrange(2) for _ in vs]
        if not any((planted>>v&1)^t for v,t in zip(vs,signs)):signs[0]^=1
        clauses.append(list(zip(vs,signs)))
    if unsat:clauses[:8]=[list(enumerate(s)) for s in product(range(2),repeat=3)]
    vals=[]
    for row in clauses:
        a,b,c=[nand(z[v],z[v]) if t else z[v] for v,t in row]
        ab=nand(nand(a,a),nand(b,b))
        vals.append(nand(nand(ab,ab),nand(c,c)))
    while len(g)<4096-2*(len(vals)-1):nand(0,0)
    v=vals[0]
    for w in vals[1:]:
        t=nand(v,w)
        v=nand(t,t)
    return g,clauses

for unsat in (False,True):
    g,cs=nonlinear(unsat)
    start=perf_counter();q=Quotient(128,g,8);mask=packed(q,65536)
    ms=1000*(perf_counter()-start)
    expected=sum(1 for x in range(65536)
                 if all(any((x>>v&1)^t for v,t in row) for row in cs))
    assert mask.bit_count()==expected and bool(expected)!=unsat
    print('CNF UNSAT' if unsat else 'CNF SAT',expected,len(q.gates),round(ms,2),'ms')

def enc_bit(n,g,b,k=8,cap=65536):
    for attempt in range(2):
        gates=g if attempt==0 else infer_order(n,g,k)[1]
        q=Quotient(n,gates,k)
        mask=packed(q,cap)
        if mask is not None:return bool(b and mask)
    return bool(b and any(evaluate(n,g,x) for x in range(1<<n)))

def dec_bit(ciphertext,witness):
    return ciphertext

for _ in range(100):
    n=r.randrange(8);s=r.randrange(12)
    g=[(r.randrange(n+s+1),r.randrange(n+s+1)) for _ in range(s)]
    sat=any(evaluate(n,g,x) for x in range(1<<n))
    for b in (0,1):
        assert dec_bit(enc_bit(n,g,b,k=2,cap=1),0)==bool(b and sat)
for reject in (False,True):
    g,_=nonlinear(reject)
    assert [enc_bit(128,g,b) for b in (0,1)]==[False,not reject]
~~~
