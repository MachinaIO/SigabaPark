---
title: Width-reduced binary clause programs with a unit output at every rejecting assignment
refs: [definition:WE_CircuitSAT, note:pq-we-live-clause-matrix-product, note:pq-we-quantum-prefix-tree]
tags: [witness-encryption, compilation, correctness, complexity]
---

**Why change the output.** The live-clause construction accumulates the number of falsified clauses. At modulus 2^k a positive even count has no multiplicative inverse. This invalidates the uniform-projection argument when that count is the only rejecting coefficient. The diagonal CNF program of [VWW Construction 6.2](https://ntt-research.com/wp-content/uploads/2023/01/Witness-encryption-and-null-iO-from-evasive-LWE.pdf) avoids the issue by retaining one failure bit per clause. Here is a middle ground: one bit per group of clauses, with a bounded read-once deterministic automaton computing whether any member fails. The groups may use overlapping witness variables. All automata read the same witness; independent group satisfiability would not suffice.

**Compiler.** Clean duplicates and tautologies. Begin with singleton groups. At each bit of an attempted merged group, keep its distinct residual clause sets after assigning that bit; a falsified clause is a permanent rejecting state. Abandon the attempted merge if a layer exceeds a public cap. Minimize the successful layered automaton backwards by assigning equal states to equal pairs of successor labels. Drop states from which no suffix can cause a clause failure, implementing them by a zero row. For each potential pair of groups consider the resulting maximum *simultaneous* state count over the layers, including one output per retained group at the end. Merge without increasing that width and break ties by the sum of states. This heuristic does not certify an optimal partition. A polynomial cap bounds each attempt and there are polynomially many attempts. A singleton non-tautological clause has at most one active state after dropping its dead state at each layer: it is still possible to falsify exactly when no literal seen so far is true. The compiler therefore never needs width greater than c+1 for c distinct non-tautological clauses. The fixed cap of at least three also admits singleton forward exploration.

**Encoding and correctness.** The initial row places a one at the start state of each active group and the message bit in a separate coordinate. Retain that coordinate by an identity transition. Allocate disjoint state slots for the groups at every layer, reusing the slot numbers across layers. Under either local input choice each active state sends one to its unique target, or disappears when it can no longer reject. In the last layer direct rejecting states to disjoint output slots. Induction gives the final integer vector (mu,fail_1,...,fail_g,0,...), where fail_i is one exactly when the supplied assignment falsifies a clause in group i. No pair of groups can cancel. On a false instance every complete path has a coefficient equal to one for either message. Thus its entries generate the unit ideal for *any* modulus q>=2, including 2^k. The property also holds for all its prefixes: any common divisor with q of an entire prefix row divides every complete extension. On a valid witness the terminal vector has just the message coordinate. This supplies the logical projection and binary-program conditions of the tensor approach. Cryptographic hiding still depends on the backend assumptions at the chosen modulus.

**Costs.** For H input bits and width w, the original tensor formulas apply. For fixed n and k=ceil(log2 q), m=2nwk makes transition payload, and full-root dense Dec product count, proportional to (H-1)w². Preimage-column counts are proportional to (H-1)w. All logical matrices have row sum at most one: every state is routed deterministically. Every subproduct therefore has maximum row sum at most one. On a prefix the logical row has 1-norm at most g+1. In the prior centered-error recurrence with absolute factor-entry cap S and injected-error cap E, the prefix source term at depth i may consequently be bounded by (g+1)(nS)^i E. This costs no factor w per propagated logical level. Actual encryption additionally pays for compilation, Gaussian preimages, and the modulus required by its security and correctness bounds. The construction gives polynomial honest work even when all merges fail.

**Controls.** On the same 60 seeded four-input, five-NAND circuits, cap four reduced the width relative to the unit-output diagonal baseline on all 60. Sum of widths dropped from 890 to 425; sum of squared widths from 13294 to 3181. At fixed common n,k and H=9 this leaves 47.8% of the preimage-column count and 23.9% of the transition payload and dense decryption products. Five circuits merged to one small automaton, in which case SAT can already be decided by public reachability. Indeed a separate public projection algorithm from the component-encoder note decides all 60 of these small circuits; this is a comparison of general-purpose matrix representations, not evidence of hard instances. Two mixed three-literal CNFs on eight and twelve variables gave widths 13 and 17 against diagonal widths 17 and 25 while retaining seven and eight groups. Sliding three-literal windows on 24 variables yielded one width-five program instead of 23 diagonal coordinates, also publicly decidable. Across 2268 witness/message trials, exact matrix evaluation recovered each individual group's failure bit, including empty-clause and empty-formula cases. An implementation can send the resulting binary program directly to the original tensor encoder; only the public variable order is needed to select branches.

Save the first listing as groups.py. The next listings reproduce exact semantic and NAND checks from the DAG root.

~~~python
def dfa(C,H,cap):
    # State is the set of remaining clauses. An empty clause is the rejecting state.
    def norm(F):
        F=tuple(F)
        if any(not c for c in F):
            return ((),)
        return tuple(sorted(set(tuple(sorted(c)) for c in F)))
    states=[norm(C)]
    trans=[]
    for i in range(1,H+1):
        new={};edges=[]
        for s in states:
            pair=[]
            for lit in (-i,i):
                key=norm(tuple(x for x in c if x!=-lit) for c in s if lit not in c)
                if key not in new:
                    if len(new)>=cap:return None
                    new[key]=len(new)
                pair.append(new[key])
            edges.append(tuple(pair))
        trans.append(edges);states=list(new)
    # Minimize layered automaton from terminal labels backwards.
    labels=[0 if s else -1 for s in states]
    layers=[]
    for edges in reversed(trans):
        ids={};rows=[]
        for x,y in edges:
            row=(labels[x],labels[y])
            rows.append(-1 if row==(-1,-1) else ids.setdefault(row,len(ids)))
        layers.append(tuple(ids))
        labels=rows
    return list(reversed(layers))

def pack_groups(clauses,H,cap=8):
    F=sorted({tuple(sorted(set(c))) for c in clauses if not any(-a in c for a in c)})
    if H<1 or cap<3 or any(x==0 or abs(x)>H for c in F for x in c):
        raise ValueError("invalid variable or cap")
    # Singleton clauses need at most three states before minimization.
    groups=[([c],dfa([c],H,cap)) for c in F]
    def width(ds):
        return 1+max([len(ds)]+[sum(len(d[j]) for d in ds) for j in range(H)])
    while len(groups)>1:
        ds=[d for C,d in groups];best=None
        for i,(C,d) in enumerate(groups):
            for k in range(i):
                together=groups[k][0]+C
                merged=dfa(together,H,cap)
                if merged is None:continue
                cand=[g for u,g in enumerate(groups) if u not in (k,i)]+[(together,merged)]
                sizes=[x[1] for x in cand]
                cost=(width(sizes),sum(len(layer) for g in sizes for layer in g))
                if cost[0]<=width(ds) and (best is None or cost<best[0]):
                    best=cost,cand
        if best is None:break
        groups=best[1]
    ds=[d for _,d in groups];w=width(ds)
    offsets=[]
    for j in range(H):
        at=1;off=[]
        for d in ds:off.append(at);at+=len(d[j])
        offsets.append(off)
    row=[0]*w
    for v,d in zip(offsets[0],ds):
        if d[0]:row[v]=1
    layers=[]
    for j,off in enumerate(offsets):
        pair=[{(0,0)},{(0,0)}]
        for k,d in enumerate(ds):
            for i,target in enumerate(d[j]):
                for b,t in enumerate(target):
                    if t<0:continue
                    if j+1<H:dst=offsets[j+1][k]+t
                    else:dst=1+k
                    pair[b].add((off[k]+i,dst))
        layers.append(pair)
    return [tuple(c) for c,_ in groups],row,layers
~~~
~~~~python
from itertools import product
from random import Random
import runpy
g=runpy.run_path('groups.py')
def reject(C,x):
    return int(any(not any(x[abs(a)-1]==(a>0) for a in c) for c in C))
def check(C,H,cap):
    groups,row,layers=g['pack_groups'](C,H,cap)
    for x in product((0,1),repeat=H):
        for mu in (0,1):
            v=row.copy();v[0]=mu
            for b,p in zip(x,layers):
                u=[0]*len(v)
                for i,j in p[b]:u[j]+=v[i]
                v=u
            assert v==[mu]+[reject(c,x) for c in groups]+[0]*(len(v)-1-len(groups))
            assert any(v[1:])==bool(reject(C,x))
    return len(groups),len(row)
rng=Random(109);cases=0
for H in range(1,7):
 for _ in range(9):
    C=[tuple(rng.randrange(1,H+1)*rng.choice((-1,1)) for _ in range(rng.randrange(4))) for j in range(rng.randrange(14))]
    check(C,H,4);cases+=2*(2**H)
print(cases)
for H in (8,12,24):
    C=[(i,i+1,i+2) for i in range(1,H-1)]
    gs,row,_=g['pack_groups'](C,H,6)
    print('windows',H,len(C)+1,len(gs),len(row))
for H in (8,12):
    C=sorted({tuple(sorted(i*rng.choice((-1,1)) for i in rng.sample(range(1,H+1),3))) for _ in range(2*H)})
    gs,row,_=g['pack_groups'](C,H,4)
    print('mixed',H,len(C)+1,len(gs),len(row))
~~~~
~~~~python
from pathlib import Path
from random import Random
import runpy
g=runpy.run_path('groups.py')
front={}
s=Path('dag/Notes/pq-we-live-clause-matrix-product.md').read_text()
exec(s.split('~~~python\n')[1].split('def run_tests')[0],front)
rng=Random(712);before=[];after=[];one=0
for _ in range(60):
    C=front['nand_cnf'](4,[(rng.randrange(5+j),rng.randrange(5+j)) for j in range(5)])
    F={tuple(sorted(set(c))) for c in C if not any(-a in c for a in c)}
    gs,row,_=g['pack_groups'](C,9,4)
    before.append(len(F)+1);after.append(len(row));one+=len(gs)==1
assert all(y<=x for x,y in zip(before,after))
print(sum(before),sum(after),sum(x*x for x in before),sum(y*y for y in after),sum(y<x for x,y in zip(before,after)),one)
~~~~
