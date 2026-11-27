---
title: Compress read-once WE depth while retaining a binary tensor backend
refs: [definition:WE_CircuitSAT, note:pq-we-live-clause-matrix-product, note:pq-we-root-loss-budget, note:pq-we-quantum-prefix-tree]
tags: [witness-encryption, compilation, complexity, correctness]
---

**Binary interval products.** Many local bit strings can act by exactly the same transition on a matrix branching program. Group consecutive witness bits when their *joint* products, evaluated in both message programs, realize at most two distinct pairs of binary matrices. A group of this kind still needs only two encrypted transitions. Use exact nonnegative integer products; a Boolean support product can discard multiplicities and give a different final value. The check on both messages together ensures that the layout, branch labels and witness projection are public, even when individual matrices depend on the message. Initial rows are carried through unchanged. This compiler composes plaintext logical matrices before encryption; the shorter encoder draws fresh independent tensor factors and new keys at its own levels.

**Finding groups.** Starting at a candidate interval's left endpoint keep the reachable set of pairs of matrix products. Extend by multiplying each pair by the two public joint choices at the next level and assigning deterministic indices to distinct results. Keep the corresponding two outgoing indices for each old state. A candidate can pass through more than two states and later collapse back to two, or through nonbinary integer products that later become binary. Enforce a public cap C>=2 on intermediate distinct states and abandon that start at its first overflow. This deliberately misses intervals that first exceed C and later merge. Among intervals admitted by this rule and the terminal binary condition, the suffix recurrence best[i]=1+min(best[j]) finds the minimum number of levels. A single original level always qualifies for binary inputs. The reference keeps endpoints during the search and regenerates routing for just the chosen partition. It takes O(H² C w³) dense arithmetic operations up to the costs of hashing/comparing matrices (a deterministic ordered dictionary also suffices). Input lookup and integer bit costs are polynomial: for binary w-by-w factors each product entry has O(1+H log(max(2,w))) bits. A constant or polynomial C gives a polynomial honest compiler. Selecting branches in the resulting public routing tables takes O(H) index lookups. If Dec lacks the public statement, transmit the routing once: for fixed C, H cut bits, a known starting index and padded transitions using at most 2HC ceil(log2 C) bits suffice, in addition to standard length framing. If the statement is already available, the routing can instead be recomputed.

**Preservation and security scope.** The projected choice selects exactly the two-message product induced by the local witness bits, so concatenation reproduces both full integer products for every original witness. Conversely every local label has a realizing substring, up to duplicate labels for a singleton state. Groups occupy disjoint positions, hence these substrings concatenate and realize *any* grouped path in both message programs. No spurious accepting zero or nonunit prefix is introduced on a false statement for which all original complete rows generate the unit ideal. Every grouped prefix is an original prefix in particular. Since the backend still receives a binary read-once program with binary transition entries, its false-instance theorem may be applied directly at the new depth, if its parameter and adversary hypotheses hold. No larger-alphabet evasive-LWE assumption is needed for this compiler. The tensor-ciphertext distributions before and after compilation can differ. Correctness, noise widths, hardness and hybrid losses must be checked at the parameters actually used. In particular the polynomial compiler preserves the underlying theorem's adversary class; it supplies no independent quantum evasive-LWE implication.

**Costs and controls.** At common full-root parameters n,m,k and grouped depth G, ciphertext residue payload is (2nm+2(G-1)m²)k, Enc draws 2(G-1)m transition preimage columns, and Dec uses (G-1)nm² scalar multiply-adds after witness projection. Encrypted setup is needed at G levels. Include the public compiler, routing and circuit-to-witness-trace costs in any end-to-end time. The root-security induction uses G-1 evasive hops and the deepest explicit prefix tree has 2^G leaves. Under distinctness or width constraints the compiler may retain all H levels.

On a control of eight disjoint OR clauses of eight variables apiece, the live-clause compiler gives H=64 and width four. With C=8 the interval compiler gives G=8, still at width four, with two encrypted choices per group. The number of preimage columns goes from 126m to 14m and the selected square matrix products from 63 to seven. Security-proof table sizes at full depth go from 2^64 to 256. This control has easy witnesses and measures representation. On 60 seeded four-input, five-NAND circuits converted by the same CNF frontend, 34 became shorter and total depth fell from 540 to 492. With fixed m the transition-block count fell from 960 to 864 across that set. These are exact counts, not timings. Exhaustive checks over every bit string of 24 small independent two-message matrix programs and six CNF controls verified both the full product equality and representability of grouped paths. The reference receives levels indexed by original position, message bit and local witness bit; its runtime and counts refer to these public logical programs.

~~~python
def mm(A,B):
    bt=tuple(zip(*B))
    return tuple(tuple(sum(x*y for x,y in zip(row,col)) for col in bt) for row in A)

def extend(states, branches, cap):
    ids={}
    route=[]
    for pair in states:
        options=[]
        for bit in (0,1):
            key=tuple(mm(pair[mu],branches[mu][bit]) for mu in (0,1))
            if key not in ids:
                if len(ids)==cap:
                    return None
                ids[key]=len(ids)
            options.append(ids[key])
        route.append(tuple(options))
    return tuple(ids),tuple(route)

def binary_states(states):
    return len(states)<=2 and all(v in (0,1) for pair in states for M in pair for row in M for v in row)

def fold(levels,w,cap=8):
    """levels[i][mu][bit] is a w-by-w binary tuple of tuples."""
    if not levels or cap<2:
        raise ValueError("nonempty program and cap >= 2 required")
    I=tuple(tuple(int(i==j) for j in range(w)) for i in range(w))
    H=len(levels)
    best=[H+1]*H+[0]
    end=[None]*H
    for start in reversed(range(H)):
        states=((I,I),)
        for i in range(start,H):
            step=extend(states,levels[i],cap)
            if step is None:
                break
            states,_=step
            if binary_states(states) and 1+best[i+1]<best[start]:
                best[start]=1+best[i+1]
                end[start]=i+1
    groups=[]
    start=0
    while start<H:
        states=((I,I),)
        route=[]
        for branches in levels[start:end[start]]:
            states,edges=extend(states,branches,cap)
            route.append(edges)
        groups.append((states+(states[-1],) if len(states)==1 else states,route))
        start=end[start]
    return groups

def project(bits,groups):
    result=[]
    j=0
    for _,route in groups:
        v=0
        for edges in route:
            v=edges[v][bits[j]]
            j+=1
        result.append(v)
    if j!=len(bits):
        raise ValueError("wrong witness length")
    return result
~~~

To reproduce the controls, save the first listing as binary_fold.py and run the next listing from the DAG repository root.
~~~~python
from pathlib import Path
from itertools import product
from random import Random
import runpy
g=runpy.run_path('binary_fold.py')
front={}
s=Path('dag/Notes/pq-we-live-clause-matrix-product.md').read_text()
exec(s.split('~~~python\n')[1].split('def run_tests')[0],front)
def make(clauses,H):
    u,edges=front['compile_program'](clauses,H,0);w=len(u)
    def dense(E):
        return tuple(tuple(int((i,j) in E) for j in range(w)) for i in range(w))
    return w,[[tuple(dense(E) for E in pair)]*2 for pair in edges]
def run(levels,w):
    groups=g['fold'](levels,w)
    reach=set()
    for x in product(range(2),repeat=len(levels)):
        z=tuple(g['project'](x,groups));reach.add(z)
        for mu in (0,1):
            A=tuple(tuple(int(i==j) for j in range(w)) for i in range(w));B=A
            for lev,b in zip(levels,x):A=g['mm'](A,lev[mu][b])
            for (p,_),b in zip(groups,z):B=g['mm'](B,p[b][mu])
            assert A==B
    # A duplicated constant choice has the same matrix pair.
    for z in product(range(2),repeat=len(groups)):
        assert tuple(0 if p[0]==p[1] else b for b,(p,_) in zip(z,groups)) in reach
    return len(groups)
r=Random(5)
for i in range(24):
    H=1+i%6;w=2
    def mat():return tuple(tuple(r.randrange(2) for _ in range(w)) for _ in range(w))
    run([[(mat(),mat()),(mat(),mat())] for j in range(H)],w)
for H in [6,8]:
    for clauses in [[tuple(range(1,H+1))],[(1,2),(-3,4),(5,-6)],[(),(1,),(-1,)]]:
        w,levels=make(clauses,H);run(levels,w)
for length in [2,4,8]:
    h=8*length;cs=[tuple(range(i+1,i+length+1)) for i in range(0,h,length)]
    w,levels=make(cs,h);groups=g['fold'](levels,w)
    print(h,w,[len(route) for _,route in groups])
rng=Random(712)
before=after=reduced=0
for i in range(60):
    gates=[(rng.randrange(5+j),rng.randrange(5+j)) for j in range(5)]
    w,levels=make(front['nand_cnf'](4,gates),9)
    k=len(g['fold'](levels,w))
    before+=len(levels)
    after+=k
    reduced+=int(k<len(levels))
assert (before,after,reduced)==(540,492,34)
~~~~
