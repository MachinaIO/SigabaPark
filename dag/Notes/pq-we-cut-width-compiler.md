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

### Sharing equal prefixes and equal suffixes of signed clauses

At a variable cut, split each crossing clause into the nonempty signed literal lists P already processed and S still unread. Fix a public orientation for each clause once for the whole program. For prefix-oriented clauses use one slot per distinct P; its value is the indicator that all literals in P were false. For suffix-oriented clauses use one slot per distinct S; its value counts clauses with that remaining suffix whose processed literals were all false. Use disjoint slot families. Allocate each cut's slot numbers independently and pad to the largest cut. The construction time, H, width and honest encryption and decryption costs remain polynomial. Arbitrary input circuits use the parent NAND trace transformation.

For each clause follow its successive slot numbers, with the source at opening and the counter at closure. Emit a binary edge on a branch whenever the current variable does not satisfy a literal of that clause. Deduplicate edges. For the prefix family an outgoing indicator has just one predecessor: remove the current literal from its prefix if present, or use the same prefix if absent. A failing completed clause corresponds to one counter edge from its preceding indicator; for a fixed branch two such clauses with identical preceding prefix and final false literal would be the same signed clause. For the suffix family, all clauses sharing an old suffix have the same continuation; transmit its count once if the branch survives. Incoming edges from distinct old suffixes add their disjoint counts. Newly opened clauses have only one possible false first literal at that variable on the branch, so two openings into an identical suffix on that branch would duplicate a complete clause. A failing singleton contributes its own source-to-counter edge. These observations give the claimed slot invariants by induction, including exact multiplicities at closure. Empty clauses and final projection are unchanged.

The backend must also control intermediate subproducts. Within the prefix family each destination slot has at most one predecessor per branch, so each slot gets at most one path from any fixed starting coordinate on any subinterval (including the source, whose sole predecessor is itself). Entries into the sink across that subinterval are bounded by the number of clause closings. In the suffix family each slot has at most one successor per branch, so each initial unit and each opening from the source can arrive at the sink at most once. There are at most as many such openings as clauses. Together with the three permanent coordinates this gives polynomial integer subproduct bounds. The original modulus choice and argument using the terminal failure count still apply; this is a new binary program for the same conditional cryptographic backend.

The compiler compares both uniform orientations, seeds based on the degrees of prefixes and suffixes at the busiest ordinary cut, and bounded passes of individual flips decreasing the sum of occupied slots over cuts. Select by measured peak and then sum among the candidates and variable orders. The chooser is polynomial even if every clause spans all variables. It does not require minimizing over all orientations. Orders must be compared with the shared-slot score: an order minimizing separate-clause width can discard profitable sharing.

On the same 4096-NAND program and 4224 levels the first-use order goes from separate width 26 to prefix width **7**. The previously refined order goes from 21 to 13. Selecting among them yields width 7 versus the previous best of 21. At equal scale m proportional to width, interior matrix entries, selected interior dense Dec multiply-adds and interior one-dimensional Gaussian draws are each one ninth of the previous best, and the number of interior sampled columns is one third. These are structural counts on the stated control, with the same endpoint and timing caveats as above. Sixteen full NAND traces, including deliberately changed gate values, are checked against the exact clause-violation count.

A fixed-order family illustrates why per-clause choice can matter. Put two disjoint n-edge stars across the same cut, the first with its shared variable on the processed side and the other with its shared variable on the unread side. Use positive clauses and open the first star center before all left leaves and close the second center after all right leaves. At the central cut there are 2n crossing clauses. Always sharing prefixes or always sharing suffixes requires n+1 slots there. Orient the first star by prefix and the second by suffix to use only two slots throughout. With n=32 the emitted widths including permanent coordinates are 67, 36, 36 and 5. This is a property of this fixed-order compiler, not a lower bound for encrypting the predicate by other means.

Save the next listing as mixed.py and run python mixed.py frontend.py cut.py. It tests both uniform orientations, arbitrary mixed orientations and the implemented selector on 16320 path/message cases. The 4096-gate comparison uses the same public order candidates as the first listing.

~~~python
"""Share prefix indicators and suffix counters in disjoint slot families."""
from collections import defaultdict,Counter
from random import Random
from itertools import product
import runpy,sys

def cuts(cs,order):
    pos={v:i for i,v in enumerate(order)}
    paths=[]
    for c in cs:
        seq=sorted((pos[abs(x)],x) for x in c)
        path=[]
        for j in range(1,len(seq)):
            p=('p',tuple(x for _,x in seq[:j]))
            s=('s',tuple(x for _,x in seq[j:]))
            path.extend((i,p,s) for i in range(seq[j-1][0],seq[j][0]))
        paths.append(path)
    return paths

def choose(paths,h):
    def descend(seed):
        counts=[Counter() for _ in range(h)]
        labels=seed.copy()
        for mode,path in zip(labels,paths):
            for row in path:counts[row[0]][row[mode+1]]+=1
        for step in range(3):
            indices=range(len(paths)) if step%2==0 else reversed(range(len(paths)))
            for idx in indices:
                old=labels[idx];new=1-old;delta=0
                for row in paths[idx]:
                    C=counts[row[0]]
                    delta+=int(C[row[new+1]]==0)-int(C[row[old+1]]==1)
                if delta>=0:continue
                for row in paths[idx]:
                    C=counts[row[0]];C[row[new+1]]+=1;C[row[old+1]]-=1
                    if not C[row[old+1]]:del C[row[old+1]]
                labels[idx]=new
        return labels
    candidates=[[m]*len(paths) for m in range(2)]
    # Orient clauses toward high-degree endpoints at the busiest ordinary cut.
    at=[[] for _ in range(h)]
    for idx,path in enumerate(paths):
        for i,p,s in path:at[i].append((idx,p,s))
    center=max(at,key=len,default=[])
    degrees=Counter(key for _,p,s in center for key in (p,s))
    for default in (0,1):
        seed=[default]*len(paths)
        for idx,p,s in center:
            seed[idx]=int(degrees[s]>degrees[p]) if degrees[s]!=degrees[p] else default
        candidates.append(seed)
    candidates += [descend(seed) for seed in candidates]
    def score(labels):
        live=[set() for _ in range(h)]
        for mode,path in zip(labels,paths):
            for row in path:live[row[0]].add(row[1+mode])
        sizes=list(map(len,live))
        return max(sizes,default=0),sum(sizes)
    return min(candidates,key=score)

def compile_mixed(cs,order,msg,paths,modes):
    pos={v:i for i,v in enumerate(order)}
    layers=[[{(0,0),(1,1),(2,2)} for _ in (0,1)] for _ in order]
    groups=[{} for _ in order]
    width=3
    for c,path,mode in zip(cs,paths,modes):
        if not c:continue
        left=0
        for i,*keys in path:
            table=groups[i];key=keys[mode]
            right=table.setdefault(key,len(table)+3)
            width=max(width,right+1)
            for bit in (0,1):
                if (order[i] if bit else -order[i]) not in c:
                    layers[i][bit].add((left,right))
            left=right
        i=max(pos[abs(x)] for x in c)
        for bit in (0,1):
            if (order[i] if bit else -order[i]) not in c:layers[i][bit].add((left,1))
    if not layers:layers=[[{(1,1),(2,2)} for _ in (0,1)]]
    layers[-1]=[{(a,b) for a,b in branch if b in (1,2)} for branch in layers[-1]]
    return [1,int(() in cs),msg]+[0]*(width-3),layers

def audit(front,cut):
    rng=Random(51231);checks=0
    for h in range(8):
        for _ in range(8):
            cs=cut['canonical']([tuple(rng.choice((-1,1))*rng.randint(1,h) for _ in range(rng.randrange(5))) if h else () for _ in range(15)])
            o=list(range(1,h+1));rng.shuffle(o);paths=cuts(cs,o)
            for mode in ([0]*len(cs),[1]*len(cs),[rng.randrange(2) for c in cs],choose(paths,h)):
                for bit in (0,1):
                    pr=compile_mixed(cs,o,bit,paths,mode)
                    for bits in product((0,1),repeat=h):
                        f=sum(not any(bits[abs(x)-1]==(x>0) for x in c) for c in cs)
                        row=front['eval_program'](pr,[bits[v-1] for v in o])
                        assert row[1]==f and row[2]==bit and sum(row)==f+bit
                        checks+=1
    print('complete path checks',checks)
    n=128;gates=[];prev=0
    for i in range(1,n+1):
        for j in range(32):
            gates.append((prev,i if j%3==0 else prev));prev=n+len(gates)
    cs=cut['canonical'](front['nand_cnf'](n,gates));sup=cut['supports'](cs)
    first=cut['first_use'](n,gates)
    for order in (first,cut['refine'](sup,first)):
        for o in (order,list(reversed(order))):
            paths=cuts(cs,o)
            modes=choose(paths,len(o))
            print('separate, prefix, suffix, selected widths:',3+cut['profile'](sup,o)[0],
                  *[len(compile_mixed(cs,o,0,paths,mode)[0]) for mode in ([0]*len(cs),[1]*len(cs),modes)])
    paths=cuts(cs,first);program=compile_mixed(cs,first,1,paths,choose(paths,len(first)))
    for test in range(16):
        trace=[1]+[rng.randrange(2) for _ in range(n)]
        for a,b in gates:trace.append(1-trace[a]*trace[b])
        if test%2:trace[rng.randint(n+1,len(trace)-1)]^=1
        errors=sum(not any(trace[abs(x)]==(x>0) for x in c) for c in cs)
        result=front['eval_program'](program,[trace[v] for v in first])
        assert result[1]==errors and result[2]==1 and sum(result)==errors+1
    # Two disjoint stars with opposite orientations across the same central cut.
    n=32;o=list(range(1,2*n+3))
    cs=cut['canonical']([(1,v) for v in range(n+2,2*n+2)]+[(v,2*n+2) for v in range(2,n+2)])
    paths=cuts(cs,o)
    widths=[len(compile_mixed(cs,o,0,paths,mode)[0]) for mode in ([0]*len(cs),[1]*len(cs),choose(paths,len(o)))]
    print('oppositely oriented stars:',3+cut['profile'](cut['supports'](cs),o)[0],widths)
if __name__=='__main__':audit(*map(runpy.run_path,sys.argv[1:]))
~~~
