---
title: Clause-cut width and local order optimization for polynomial matrix witness encryption
refs: [definition:WE_CircuitSAT, note:pq-we-live-clause-matrix-product]
tags: [witness-encryption, compilation, complexity, branching-programs]
---

The general NAND compiler in the referenced note reserves one matrix coordinate for each closed clause interval incident to a level. Input and output coordinates of a transition are separate copies of the space. Consequently a clause ending on the present variable and a clause beginning there may use the same coordinate number. This saves width even with the variable order fixed. A second improvement chooses the order using the public circuit before encryption.

**Construction.** Keep the original source, failure accumulator and message coordinates. Across the cut after the first i variables keep one slot for each nonsingleton clause having at least one variable on each side. Its value is one exactly when every literal already read was false. At a variable, keep slots for continuing clauses and assign the newly opened clauses arbitrary free slots, including those just retired. A transition branch carries a clause value only if the current bit does not satisfy that clause at this variable. Read the source at opening and the old slot otherwise. Write the counter at closing and the new slot otherwise. Deduplicate signed clauses and handle the empty clause, singletons and the final projection as in the original compiler. On each branch there is at most one failed singleton. An opening goes from the source to a unique destination slot and a closing reads a unique old slot, so reusing numeric labels cannot conflate edges. Induction gives the same terminal failure count and message. For either message, all transition matrices remain binary. Intermediate entries for arbitrary subpaths are still bounded by a polynomial: only the source can open fresh slots, each internal slot has at most one continuation, and a closing can only enter the accumulating sink. The same VWW parameter and security obligations as the original compiler apply.

If the largest clause cut has size C, the emitted width is exactly 3+C, with the three designated permanent coordinates. This is the workspace needed by this explicit one-slot-per-crossing-clause layout. The width of more general branching programs may be smaller. On large or sparse wire indices compact the used input and gate labels as in the parent note and charge the cost of reading the original encoding. The trace is computed in circuit order and reordered only after gate evaluation. No secret input is used to choose the order.

**Order selection.** Include the original order, first use of each input during the ordinary gate scan, and local refinements. An order can be scored by a difference array over the first and last occurrence of each clause. Within a fixed window hold the rest of the order fixed. For a subset of processed window variables the cut cost is determined by the subset alone. Clauses disjoint from the window contribute a constant inside it. Compute the smallest possible maximum cut by the subset recurrence taking the maximum of the current cut and the smallest predecessor peak. Under that optimal peak run a second subset recurrence minimizing the sum of cuts. Backtrack to recover an order. The listing uses windows of six, three passes and an incumbent checked using the whole order. Local optimality within one optimized window does not imply global optimality. With fixed window size b this is polynomial; subset work per window is O(2^b (b+number of incident clauses)) for bounded arity, apart from preprocessing. The explicit dense output or the sparse edge lists can both be produced in polynomial time. Compare scored candidate orders before compiling the chosen one. The audit compiles each separately for independent validation.

**4096 NAND gates and 128 inputs.** On the streaming control of the parent note, its hand-interleaved closed-interval compiler used width 28. The new cut compiler measured 2819 in input-first order, 26 with automatically generated first-use order and 21 after the bounded window search. Both the original hand order and the refined order have 4224 layers. At equal tensor dimension, modulus, root rows, terminal columns and a common m proportional to width, reducing width from 28 to 21 cuts interior ciphertext entries and the selected dense interior Dec multiply-add count by exactly 43.75%. Interior preimage column count falls by 25%, and a dense nearest-plane implementation's one-dimensional Gaussian draws on those columns fall by 43.75%. These counts exclude order search, trapdoor setup and endpoint terms. They are structural estimates for matrix encoding. The control also admits a bounded SAT shortcut. No concrete quantum hardness, end-to-end time or global submission clock is inferred.

Run python cut.py frontend.py with the first listing of the parent note as frontend.py. The reference checks 2540 complete path/message outputs including degenerate clauses and empty statements. It compares the optimized (peak,area) with unrestricted permutation search on every control of at most five variables, and checks each large emitted width against its independently counted peak.

~~~python
"""Use one slot per clause crossing a variable cut; refine bounded order windows."""
from collections import defaultdict
from itertools import permutations,product
from random import Random
import runpy
import sys

def canonical(clauses):
    return sorted({tuple(sorted(set(c))) for c in clauses if not any(-x in c for x in c)})

def supports(cs):
    return [set(map(abs,c)) for c in cs if len(c)>1]

def profile(sup,order):
    pos={v:i for i,v in enumerate(order)}
    delta=[0]*(len(order)+1)
    for c in sup:
        indices=[pos[v] for v in c]
        delta[min(indices)]+=1
        delta[max(indices)]-=1
    counts=[];live=0
    for change in delta[:-1]:
        live+=change
        counts.append(live)
    return (max(counts,default=0),sum(counts))

def refine(sup,order,window=6):
    order=list(order)
    incident=defaultdict(list)
    for i,c in enumerate(sup):
        for v in c:incident[v].append(i)
    incumbent=order.copy();score=profile(sup,order)
    for offset in (0,window//2,0):
        pos={v:i for i,v in enumerate(order)}
        for start in range(offset,len(order),window):
            part=order[start:start+window]
            width=len(part);end=start+width
            if width<2:continue
            local={v:1<<j for j,v in enumerate(part)}
            clauses={i for v in part for i in incident[v]}
            terms=defaultdict(int)
            for i in clauses:
                c=sup[i]
                terms[(sum(local.get(v,0) for v in c),any(pos[v]<start for v in c),
                       any(pos[v]>=end for v in c))]+=1
            full=(1<<width)-1
            cuts=[0]*(full+1);peak=[0]*(full+1)
            for mask in range(1,full+1):
                cuts[mask]=sum(count for (bits,left,right),count in terms.items()
                               if (left or bits&mask) and (right or bits&~mask))
                predecessors=[mask^(1<<j) for j in range(width) if mask&(1<<j)]
                peak[mask]=max(cuts[mask],min(peak[sub] for sub in predecessors))
            area=[None]*(full+1);area[0]=0;parent=[0]*(full+1)
            for mask in range(1,full+1):
                if cuts[mask]>peak[full]:continue
                choices=[(area[mask^(1<<j)],j) for j in range(width)
                         if mask&(1<<j) and area[mask^(1<<j)] is not None]
                if choices:
                    value,j=min(choices);area[mask]=value+cuts[mask];parent[mask]=j
            mask=full;rev=[]
            while mask:
                j=parent[mask];rev.append(part[j]);mask^=1<<j
            order[start:end]=reversed(rev)
        candidate=profile(sup,order)
        if candidate<score:incumbent=order.copy();score=candidate
    return incumbent

def compile_cut(cs,order,msg):
    pos={v:i for i,v in enumerate(order)}
    starts=defaultdict(list)
    for clause in cs:
        if clause:starts[min(pos[abs(v)] for v in clause)].append(clause)
    live={};width=3;layers=[]
    for i,v in enumerate(order):
        outgoing={c:s for c,s in live.items() if max(pos[abs(x)] for x in c)>i}
        occupied=set(outgoing.values())
        free=[s for s in range(3,width) if s not in occupied]
        for c in starts[i]:
            if len(c)>1:
                if free:outgoing[c]=free.pop()
                else:outgoing[c]=width;width+=1
        options=[]
        for bit in (0,1):
            literal=v if bit else -v
            edges={(0,0),(1,1),(2,2)}
            for c in (*live,*starts[i]):
                if literal not in c:
                    edges.add((live.get(c,0),outgoing.get(c,1)))
            options.append(edges)
        layers.append(options);live=outgoing
    if not layers:layers=[[{(1,1),(2,2)}]*2]
    layers[-1]=[{(a,b) for a,b in branch if b in (1,2)} for branch in layers[-1]]
    return [1,int(() in cs),msg]+[0]*(width-3),layers

def first_use(n,gates):
    order=[];seen=set()
    for j,(a,b) in enumerate(gates,n+1):
        for v in (a,b,j):
            if 0<v<=j and v not in seen:
                order.append(v);seen.add(v)
    return order+[v for v in range(1,n+len(gates)+1) if v not in seen]

def audit(front):
    rng=Random(66481);tests=0
    for h in range(7):
        for trial in range(10):
            cs=canonical([tuple(rng.choice((-1,1))*rng.randrange(1,h+1) for _ in range(rng.randrange(4)))
                          if h else () for _ in range(12)])
            sup=supports(cs);o=list(range(1,h+1));rng.shuffle(o)
            o=refine(sup,o)
            if h<=5:assert profile(sup,o)==min(profile(sup,p) for p in permutations(o))
            for msg in (0,1):
                compiled=compile_cut(cs,o,msg)
                assert len(compiled[0])==3+profile(sup,o)[0]
                for bits in product((0,1),repeat=h):
                    path=[bits[v-1] for v in o]
                    row=front['eval_program'](compiled,path)
                    failures=sum(not any(bits[abs(x)-1]==(x>0) for x in c) for c in cs)
                    assert row[1]==failures and row[2]==msg and sum(row)==failures+msg
                    tests+=1
    print('exact path and message checks',tests)
    n=128;gates=[];prev=0
    for i in range(1,n+1):
        for j in range(32):
            gates.append((prev,i if j%3==0 else prev));prev=n+len(gates)
    cs=canonical(front['nand_cnf'](n,gates));sup=supports(cs)
    identity=list(range(1,n+len(gates)+1))
    first=first_use(n,gates)
    for name,o in [('input-first',identity),('first-use',first),('refined',refine(sup,first))]:
        peak,area=profile(sup,o)
        compiled=compile_cut(cs,o,0)
        assert len(compiled[0])==peak+3
        print(name,'width and sum of cut sizes',peak+3,area)
if __name__=='__main__':audit(runpy.run_path(sys.argv[1]))
~~~
