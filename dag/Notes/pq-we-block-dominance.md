---
title: Reduce both AFV tables by projecting witnesses and retaining dominating blocks
refs: [definition:WE_CircuitSAT, note:pq-we-split-witness-abe, theorem:AdvancedEncryption.WE.IPE.block_dominance_cover]
tags: [witness-encryption, predicate-encryption, circuit-sat, preprocessing]
---

The [binary inner-product compiler in PR #88](https://github.com/MachinaIO/SigabaPark/pull/88) can pay for a single key or ciphertext that serves many witnesses even when they have different crossing profiles. The decryption algorithm maps the given witness to a covering tuple of attainable representatives. After this change the local tuple ranks give ordinary table addresses. All preprocessing depends on the public circuit. The PE construction, its selective hybrid on false instances and its need for a concrete quantum LWE reduction remain as in the parent note.

**Project before choosing the cut.** Given an exact CNF for the raw NAND relation, eliminate a variable v by replacing its positive and negative clauses by every non-tautological resolvent between the two lists, removing duplicate and subsumed clauses. The example accepts a pivot only when its new resolvents have width at most eight and the clause count does not increase. This is [bounded variable elimination](https://cca.informatik.uni-freiburg.de/papers/EenBiere-SAT05.pdf). A model of the original formula restricts to a residual model. For the reverse direction, replay the pivots backwards. Set v true if some positive clause needs it. A negative clause that also needed v false would give a falsified resolvent; a tautological resolvent cannot be falsified. Otherwise v can be false. This global projection can eliminate inputs appearing on *both* sides of crossing constraints, which the parent note's local forgetting step could not do. Width, conversion to CNF, candidate scans, and intermediate resolvent generation require public work limits in an actual machine. The compiler can keep the last exact residual when a limit is encountered.

**Represent a block by the clauses it satisfies.** Start with the two assignments to each surviving variable. A row contains its clause-coverage mask and one attaining assignment on the block. The union of masks must cover all clauses. Keep only inclusion-maximal masks, with one attaining assignment for each. Any discarded row can be replaced by a retained superset with all other blocks fixed. Conversely every retained row is attainable. The Lean theorem block_dominance_cover proves the general existence equivalence. A finite compiler maps a concrete witness by finding the first dominating row in its public list.

Discharge a clause when every row of some block covers it; forget the corresponding bit in all blocks. When only one block can cover a clause, discard its rows that miss it. If no block can cover an outstanding clause or any block becomes empty, the branch is publicly NO. Merge two blocks **within one side** by taking unions of coverage masks and assignments on disjoint variables. Remove dominated rows again. A bound on pair products (64 below) controls the candidate list at each merge; stop while several blocks remain. In the prototype, each merge maximizes the number of shared live clause bits divided by the pair-product size among eligible blocks. For any satisfying witness follow its initially selected rows, choose dominating replacements, and combine its two rows on each merge. The tuple always covers the live clauses. Discharged clauses stay satisfied by every later tuple: their discharging block's assignments survive only by selection or combination. For a false instance, a pair of final tuples satisfying the residual clauses would itself be a residual model and would lift to an original witness.

**Index only useful tuples.** On each side, enforce its local clauses before issuing the entries. Recompute masks from actual retained assignments, including discharged clauses. Process blocks in an order chosen to minimize the number of clause bits straddling processed and future blocks. For each mask of previously satisfied *future* clauses keep its number of histories. For each next row, take the union, require coverage of every clause leaving the frontier, and erase those bits. Count equal next masks with their multiplicities. This computes the exact number of accepted tuples. A reverse pass computes suffix completion counts for each reachable state. Rank and unrank scan the next block’s rows, using child completion counts as disjoint interval lengths. After preprocessing, each conversion examines at most the sum of block-domain sizes in row choices, independent of the billions of table entries. Distinct tuples can still induce identical PE vectors. The witness procedure returns the tuple used for ranking; no search over an exponential WE table is required. The two passes, mask lookups, large integer arithmetic and storage of the layers enter a machine clock.

When a layer exceeds its public state cap (200,000 here), retry with fewer local clauses. Encode all omitted local tests of one side with one additional binary coordinate: set that side's bit to the OR of their violations and the opposite bit to one. Apply independently to either side and require q greater than the resulting total dimension. This preserves zero-dot compatibility even if all local clauses are omitted. A known zero count yields a public NO mode. The construction may select its orientation and a cheaper fallback from public resource caps. For ordinary one-bit WE, a bounded public SAT solver can send the bit in the clear on certified YES and a constant on certified NO. This option should be costed before PE.

### Counts on the earlier controls

These are exact rank-domain counts; billions of cryptographic entries were not generated. Use the #88 planted 128-input, 300-clause control represented by 4096 NAND gates, and its separate crossing-contradiction control. Projection leaves 84 variables and 232 clauses on YES, 81 variables and 233 clauses on NO. Start from the same 67/61 partition; transfer original coordinates 14 and 112 from its first side to its second, dropping eliminated variables. Put the smaller first side on ciphertexts. The two moves were selected on the public YES example in a cut search; they are reproducible candidate cuts, not a uniform speed claim.

| Instance and method | AFV keys | AFV ciphertexts | Dimension |
|---|---:|---:|---:|
| YES, parent single-use projection | 570808747385608 | 41923871289682 | 117 |
| YES, global projection and new cut, no dominating-block step | 145900242092 | 8052145024 | 113 |
| YES, global projection, new cut and dominating blocks | 74135796492 | 3978113712 | 113 |
| NO, parent single-use projection | 429125273565376 | 33507597876906 | 111 |
| NO, global projection, new cut and dominating blocks | 77359273476 | 2261409272 | 111 |

On YES the block step alone cuts both table lengths roughly in half at fixed cut. Relative to the parent, the full changes cut ciphertext count by a factor of 10,539 and key count by 7,700 (rounded). The static proxy 2K+(p+1)C for the two key halves and projected ciphertext vectors improves by a factor of 10,118; key coordinates and ciphertext residues can have different bit widths, and this proxy excludes setup and scalar terms. A public cap C<=3,978,113,712 makes the elementary squared-advantage hybrid floor ceil(128+2 log2 C)=192 bits, before charging reduction time, key queries and statistical losses. Use the branch only if its actual public dimensions, counts and work bounds fit. These numbers leave billions of entries and give no complete secure parameter set.

The same planted YES instance is solved in 58 nodes by the public unit-propagating DPLL control. A direct public decision is cheaper there. On the supplied NO, DPLL exhausted 4,096 nodes, although inspecting the eight planted contradictory clauses gives a short public refutation. For denser planted 460- and 540-clause controls at n=128 with the contiguous 64/64 cut, DPLL exhausted 32 nodes. The frontier cap forced the omitted-clause step: the resulting dimensions were 191 and 205. For 460 clauses the two domains had 30,074,174,869,340,160 and 2,124,861,092,895,424 entries. For 540 they had 65,223,577,434,193,920 and 91,506,452,749,352,960 entries. These controls exceed the proposed ciphertext cap in either orientation. Their public benchmark formulas are not claimed to be hard.

An inexpensive dispatcher makes the easy controls actionable. Look up pairs (U OR a), (U OR NOT a) by hashing clauses. Replace such a pair by U and remove its supersets. This preserves the truth value on *every assignment* and removes at least one clause per replacement. Repeating it seven times leaves only the empty clause on the NO control. Run the unit-propagating solver with 256 search nodes on the simplified input. The YES control returns YES in 58 nodes and the simplified NO returns NO at the root. This public branch uses **zero AFV entries on both controls**. The 460-clause control also returns YES in 39 nodes. The 540-clause control reaches the node cap and still needs a fallback. These are observations on specific public inputs; the cryptographic path's counts above describe what can be used when the public decision is skipped or inconclusive. The listing additionally checks sibling replacement for all 256 subfamilies of the eight signed ternary clauses on three inputs.

A control reaching the bounded solver's fallback can still have smaller tables. Generate 355 planted clauses over 80 active inputs, within the 128-input vocabulary. Seed 655 was the first in the scanned range starting at 650 to exceed the 256-node decision cap after sibling simplification. One sibling pair reduces the formula to 354 clauses. Using the first 36 variables on ciphertexts gives 1,487,594,368 ciphertexts and 7,749,915,736 keys in dimension 132. No local test was omitted. The local counts before block dominance are identical on this cut; here the smaller active input count and local restrictions account for the sizes. Raising the public solver cap yields YES in 503 nodes. The experiment illustrates a public dispatch tradeoff and provides no evidence that this instance is hard.

### Reproduction

Run the Python 3 listing below. It exhaustively checks all assignments on 100 small generated CNFs, including empty clauses, tautologies and absent variables. It tests projection and reverse extension, witness transport, exact rank domains, both rank directions and the omitted-clause coordinates. The large control checks selected ranks including the final rank and, on YES, the transformed planted witness. The Lean result concerns the coverage equivalence; the Python compiler and its resource accounting are not formalized.

~~~python
from collections import Counter, defaultdict
from functools import reduce
from itertools import product
from math import prod, log2
from operator import or_, and_
from random import Random


def maxima(states):
    rows={}
    for s,x in sorted(states.items(),key=lambda sx:(-sx[0].bit_count(),sx[0])):
        if all(s & ~t for t in rows):
            rows[s]=x
    return rows

def compress(F,left,n,cap,witness=None):
    # Each entry is a clause-coverage mask and an attaining assignment.
    live=(1<<len(F))-1
    blocks=[]; target=[]; owners=[{i+1} for i in range(n)]
    for j in range(n):
        v=j+1
        neg=sum(1<<i for i,c in enumerate(F) if -v in c)
        pos=sum(1<<i for i,c in enumerate(F) if v in c)
        blocks.append((v in left,{neg:0,pos:1<<j}))
        target.append(pos if witness is not None and witness>>j&1 else neg)
    merges=0; biggest=0
    while True:
        possible=[reduce(or_,s,0) for _,s in blocks]
        if reduce(or_,possible,0)&live!=live:return None
        universal=reduce(or_,(reduce(and_,s) for _,s in blocks),0)
        if universal & live:
            live &= ~universal
        seen=multi=0
        for mask in possible:
            multi |= seen&mask; seen |= mask
        changed=False
        for i,(side,rows) in enumerate(blocks):
            required=live & possible[i] & ~multi
            active={s&live:x for s,x in rows.items() if s&required==required}
            new=maxima(active)
            if not new:return None
            if witness is not None:
                wanted=target[i]&live
                target[i]=next(t for t in new if not wanted&~t)
            changed |= new.keys()!=rows.keys()
            blocks[i]=(side,new)
        if changed:continue
        if not live:break
        best=None
        for i,(side,rows) in enumerate(blocks):
            for j in range(i):
                other,cols=blocks[j];pairs=len(rows)*len(cols)
                shared=(possible[i]&possible[j]&live).bit_count()
                if side!=other or not shared or pairs>cap:continue
                score=(shared/pairs,shared,-pairs,-i,-j)
                if best is None or score>best[0]:best=score,i,j
        if best is None:break
        _,i,j=best;side,rows=blocks[i];cols=blocks[j][1]
        biggest=max(biggest,len(rows)*len(cols));merges+=1
        blocks[j]=(side,maxima({s|t:x|y for s,x in rows.items() for t,y in cols.items()}))
        if witness is not None:
            wanted=target[i]|target[j]
            target[j]=next(t for t in blocks[j][1] if not wanted&~t)
        owners[j]|=owners[i]
        del blocks[i],target[i],owners[i]
    if witness is not None:
        reconstructed=reduce(or_,(s[t] for (_,s),t in zip(blocks,target)),0)
        assert all(any(bool(reconstructed>>(abs(a)-1)&1)==(a>0) for a in c) for c in F)
    sizes=[prod(len(rows) for tag,rows in blocks if tag==side) for side in [True,False]]
    return sizes,live.bit_count(),merges,biggest,blocks,owners,(reconstructed if witness is not None else None)

def planted(n,d,seed):
    g=Random(seed); w=g.getrandbits(n);F=[]
    for _ in range(d):
        c=[v if g.randrange(2) else -v for v in g.sample(range(1,n+1),3)]
        if not any(bool(w>>(abs(v)-1)&1)==(v>0) for v in c):c[0]*=-1
        F.append(c)
    return w,F

def improve(rows):
    from collections import Counter
    r=Random(862)
    masks=[sum(1<<(i-1) for i in set(map(abs,row))) for row in rows]
    def score(L):
        left=sum(v&L==v for v in masks)
        right=sum(v&L==0 for v in masks)
        return min(left,right),left+right
    L=(1<<64)-1
    best=score(L)
    for _ in range(15000):
        i,j=r.sample(range(128),2)
        if ((L>>i)^(L>>j))&1:
            z=L^(1<<i)^(1<<j)
            s=score(z)
            if s>=best:L,best=z,s
    return {i+1 for i in range(128) if L>>i&1}

def simplify(clauses):
    keep=[]
    for c in sorted(set(clauses),key=lambda c:(len(c),tuple(sorted(c)))):
        if not any(k<=c for k in keep):keep.append(c)
    return set(keep)

def project(rows,n,width,growth):
    F=simplify(frozenset(c) for c in rows if not any(-a in c for a in c))
    trace=[]; peak=len(F)
    while F and frozenset() not in F:
        pos={};neg={}
        for c in F:
            for a in c:(pos if a>0 else neg).setdefault(abs(a),[]).append(c)
        best=None
        for v in sorted(pos.keys()|neg.keys()):
            A,B=pos.get(v,[]),neg.get(v,[])
            new=set()
            for a in A:
                for b in B:
                    h=(a|b)-{v,-v}
                    if not any(-w in h for w in h):new.add(h)
            if any(len(h)>width for h in new):continue
            new-=F
            cost=len(new)-len(A)-len(B)
            if cost>growth:continue
            score=(cost,max(map(len,new),default=0),len(new),v)
            if best is None or score<best[0]:best=score,v,A,B,new
        if best is None:break
        _,v,A,B,new=best
        trace.append((v,A))
        F=simplify((F-set(A)-set(B))|new)
        peak=max(peak,len(F))
    return F,trace,peak

def shrink(F,L,n):
    vs=sorted({abs(a) for c in F for a in c})
    ids={v:j+1 for j,v in enumerate(vs)}
    return [[ids[abs(a)]*(1 if a>0 else -1) for a in c] for c in F],{ids[v] for v in L if v in ids},vs

def stars(edges):
    # Minimum vertex cover of the bipartite graph by alternating paths.
    adj=defaultdict(set)
    for i,j in edges:adj[i].add(j)
    match={}
    def aug(i,seen):
        for j in sorted(adj[i]):
            if j in seen:continue
            seen.add(j)
            if j not in match or aug(match[j],seen):
                match[j]=i
                return True
        return False
    for i in sorted(adj):aug(i,set())
    left=set(adj)-set(match.values())
    stack=list(left);right=set()
    while stack:
        i=stack.pop()
        for j in adj[i]:
            if j in right or match.get(j)==i:continue
            right.add(j)
            if j in match and match[j] not in left:
                left.add(match[j]);stack.append(match[j])
    chosen=set(adj)-left
    row=defaultdict(set);col=defaultdict(set)
    for i,j in sorted(set(edges)):
        if i in chosen:row[i].add(j)
        else:
            assert j in right
            col[j].add(i)
    cover=[((i,),tuple(sorted(xs))) for i,xs in row.items()]
    cover += [(tuple(sorted(xs)),(j,)) for j,xs in col.items()]
    assert len(cover)==len(match)
    return cover

def compile_cnf(n,F,L):
    R=set(range(1,n+1))-L
    loc=[[],[]];edges=set()
    for clause in F:
        if any(-v in clause for v in clause):continue
        a=tuple(sorted(set(v for v in clause if abs(v) in L)))
        b=tuple(sorted(set(v for v in clause if abs(v) in R)))
        if not b:loc[0].append(a)
        elif not a:loc[1].append(b)
        else:edges.add((a,b))
    cover=stars(edges)
    return loc,edges,cover

def index(blocks,F,vs,limit=200000):
    local=sum(1<<i for i,c in enumerate(F) if all(abs(a) in vs for a in c))
    # Recompute local coverage from the attaining assignments. The compressor
    # projects away settled bits; they were discharged by their recorded blocks.
    choices=[]
    for variables,assignments in blocks:
        rows=[]
        for x in assignments:
            rows.append(sum(1<<i for i,c in enumerate(F) if local>>i&1 and any(
                abs(a) in variables and bool(x>>(abs(a)-1)&1)==(a>0) for a in c)))
        choices.append(rows)
    todo=[reduce(or_,rows,0) for rows in choices]
    if local&~reduce(or_,todo,0):return 0,0,None
    order=[];past=0
    remaining=set(range(len(todo)))
    while remaining:
        def score(i):
            future=reduce(or_,(todo[j] for j in remaining if j!=i),0)
            return ((future&(past|todo[i])).bit_count(),len(set(choices[i])),i)
        i=min(remaining,key=score);order.append(i);past|=todo[i];remaining.remove(i)
    suffix=[0]*(len(order)+1)
    for j in reversed(range(len(order))):suffix[j]=suffix[j+1]|todo[order[j]]
    counts={0:1};peak=1; layers=[counts]
    for j,i in enumerate(order):
        need=suffix[j]&~suffix[j+1]
        distinct=Counter(choices[i]); nxt=Counter()
        for old,num in counts.items():
            for mask,mult in distinct.items():
                together=old|mask
                if need&~together:continue
                nxt[together&suffix[j+1]]+=num*mult
                if len(nxt)>limit:raise OverflowError
        counts=nxt;layers.append(counts);peak=max(peak,len(nxt))

    def transition(j,old,mask):
        together=old|mask
        if suffix[j]&~suffix[j+1]&~together:return None
        return together&suffix[j+1]
    # Reverse completion counts support indexes without scanning predecessor states.
    ways=[{} for _ in layers]; ways[-1]={0:1}
    for j in reversed(range(len(order))):
        mult=Counter(choices[order[j]])
        for old in layers[j]:
            weight=sum(n*ways[j+1].get(transition(j,old,mask),0) for mask,n in mult.items())
            if weight:ways[j][old]=weight
    assert ways[0].get(0,0)==counts.get(0,0)
    def convert(x,unrank):
        if unrank and not 0<=x<counts.get(0,0):raise ValueError
        rank=old=output=0
        for j,i in enumerate(order):
            variables,rows=blocks[i]
            desired=None if unrank else x & sum(1<<(v-1) for v in variables)
            for assignment,mask in zip(rows,choices[i]):
                dest=transition(j,old,mask)
                num=ways[j+1].get(dest,0)
                if num and (x<num if unrank else assignment==desired):
                    old=dest;output|=assignment;break
                if unrank:x-=num
                else:rank+=num
            else:raise ValueError
        return output if unrank else rank
    return counts.get(0,0),peak,convert


def experiment(F,L,w,cap=64,limit=200000):
    residual,trace,peak=project(F,128,8,0)
    rows,left,vs=shrink(residual,L,128)
    if [] in rows:return 'NO'
    w2=None if w is None else sum((w>>(v-1)&1)<<i for i,v in enumerate(vs))
    result=compress(rows,left,len(vs),cap,w2)
    if result is None:return 'NO'
    sizes,live,merges,largest,blocks,owners,mapped=result
    ix=[]; extra=0
    for side,these in [(True,left),(False,set(range(1,len(vs)+1))-left)]:
        basis=[(v,list(states.values())) for (tag,states),v in zip(blocks,owners) if tag==side]
        local=sorted((c for c in rows if all(abs(a) in these for a in c)),
                     key=lambda c:(len(c),tuple(sorted(c))))
        keep=local
        while True:
            try:
                num,peakstates,convert=index(basis,keep,these,limit)
                break
            except OverflowError:
                keep=keep[:len(keep)//2]
        extra+=int(len(keep)!=len(local))
        if not num:return 'NO'
        for j in {0,num//2,num-1}:assert convert(convert(j,True),False)==j
        if w is not None:
            z=mapped & sum(1<<(v-1) for v in these)
            assert convert(convert(z,False),True)==z
        ix.append((num,peakstates,len(keep),len(local)))
    dimension=len(compile_cnf(len(vs),rows,left)[2])
    return len(vs),len(rows),dimension+extra,ix

def satisfies(F,x):
    return all(any(bool(x>>(abs(a)-1)&1)==(a>0) for a in c) for c in F)

def terminal(cover,side,assignment,omissions):
    vector=[int(any(not satisfies([sub],assignment) for sub in edges[side]))
            for edges in cover]
    for owner,clauses in enumerate(omissions):
        if clauses:
            vector.append(int(not satisfies(clauses,assignment)) if side==owner else 1)
    return vector

def validate():
    g=Random(680)
    for t in range(100):
        n=g.randint(1,7);left={v for v in range(1,n+1) if g.randrange(2)}
        F=[[g.choice((-1,1))*g.randint(1,n) for _ in range(g.randint(0,4))]
           for _ in range(g.randrange(16))]
        residual,trace,_=project(F,n,3,0)
        solutions=[x for x in range(1<<n) if satisfies(F,x)]
        vs={abs(a) for c in residual for a in c};vm=sum(1<<(v-1) for v in vs)
        for z in range(1<<n):
            if z&~vm:continue
            assert satisfies(residual,z)==any((x&vm)==z for x in solutions)
            if satisfies(residual,z):
                x=z
                for v,A in reversed(trace):
                    if any(not satisfies([a-{v}],x) for a in A):x|=1<<(v-1)
                assert satisfies(F,x)
        local,_,cover=compile_cnf(n,F,left)
        omissions=[side[::2] for side in local]
        for x in range(1<<n):
            a,b=[terminal(cover,i,x,omissions) for i in (0,1)]
            assert satisfies(F,x)==(all(satisfies(side[1::2],x) for side in local)
                                   and not any(v*u for v,u in zip(a,b)))
        projected=compress(F,left,n,16)
        if not projected:
            assert not solutions;continue
        _,_,_,_,blocks,owners,_=projected
        combined=[]
        for side,these in [(True,left),(False,set(range(1,n+1))-left)]:
            basis=[(v,list(s.values())) for (tag,s),v in zip(blocks,owners) if tag==side]
            num,_,cv=index(basis,F,these)
            local=[c for c in F if all(abs(a) in these for a in c)]
            expected={reduce(or_,t,0) for t in product(*(ss for _,ss in basis)) if satisfies(local,reduce(or_,t,0))}
            got={cv(i,True) for i in range(num)}
            assert got==expected and all(cv(cv(i,True),False)==i for i in range(num))
            combined.append(got)
        for x in solutions:
            y=compress(F,left,n,16,x)[6]
            assert any(y==(a|b) for a in combined[0] for b in combined[1])
        assert bool(solutions)==any(satisfies(F,a|b) for a in combined[0] for b in combined[1])

if __name__=='__main__':
    validate()
    w,F=planted(128,300,851);L=improve(F)|{12,76,36}
    cross=[i for i,c in enumerate(F) if any(abs(a) in L for a in c) and any(abs(a) not in L for a in c)]
    negative=F.copy()
    triple=sorted(L)[:2]+sorted(set(range(1,129))-L)[:1]
    for i,signs in zip(cross,product((-1,1),repeat=3)):
        negative[i]=[a*b for a,b in zip(triple,signs)]
    for tag,rows,wit in [('yes',F,w),('no',negative,None)]:
        for move in [set(),{14},{14,112}]:
            try:print(tag,sorted(move),experiment(rows,L-move,wit),flush=True)
            except OverflowError:print(tag,sorted(move),'frontier cap',flush=True)

def public_probe(rows,limit):
    # Bounded exact SAT decision. On exhaustion the encryption chooses its fallback.
    F=tuple(frozenset(c) for c in rows if not any(-a in c for a in c))
    used=0
    def search(F):
        nonlocal used
        if used>=limit:return None
        used+=1
        while F:
            c=min(F,key=len)
            if not c:return False
            if len(c)>1:break
            a=next(iter(c));F=tuple(c-{-a} for c in F if a not in c)
        if not F:return True
        freq=Counter(a for c in F for a in c)
        a=max(freq,key=lambda a:(freq[a]+freq[-a],freq[a],a))
        first=search(tuple(c-{-a} for c in F if a not in c))
        if first is not False:return first
        return search(tuple(c-{a} for c in F if -a not in c))
    return search(F),used

if __name__=='__main__':
    for name,rows in [('yes',F),('no',negative)]:
        print('public DPLL',name,public_probe(rows,32),public_probe(rows,4096))
    for total in (460,540):
        witness,harder=planted(128,total,851)
        try:answer=experiment(harder,set(range(1,65)),witness)
        except OverflowError:answer='frontier cap'
        print(total,public_probe(harder,32),answer)


if __name__=='__main__':
    residual,_,_=project(F,128,8,0)
    rows,left,vs=shrink(residual,L-{14,112},128)
    for side in (left,set(range(1,len(vs)+1))-left):
        basis=[({v},[0,1<<(v-1)]) for v in sorted(side)]
        print('without block dominance',index(basis,rows,side)[:2])

def sibling_closure(rows):
    F={frozenset(c) for c in rows if not any(-a in c for a in c)}
    steps=0
    while True:
        redex=next(((c,a) for c in sorted(F,key=lambda c:(len(c),tuple(sorted(c))))
                    for a in sorted(c) if (c-{a})|{-a} in F),None)
        if redex is None:break
        c,a=redex;short=c-{a}
        F={d for d in F if not short<=d}|{short}
        steps+=1
    return F,steps

if __name__=='__main__':
    for name,base in [('yes',F),('no',negative)]+[(str(t),planted(128,t,851)[1]) for t in (460,540)]:
        simplified,steps=sibling_closure(base)
        ordered=[tuple(sorted(c)) for c in sorted(simplified,key=lambda c:(len(c),tuple(sorted(c))))]
        print('dispatch',name,steps,len(ordered),public_probe(ordered,256))
    triples=list(product((-1,1),repeat=3))
    core=[tuple(a*b for a,b in zip((1,2,3),signs)) for signs in triples]
    for mask in range(256):
        raw=[c for i,c in enumerate(core) if mask>>i&1]
        out,_=sibling_closure(raw)
        assert all(satisfies(out,x)==satisfies(raw,x) for x in range(8))

if __name__=='__main__':
    w80,F80=planted(80,355,655)
    simp,_=sibling_closure(F80)
    ordered=sorted((tuple(sorted(c)) for c in simp),key=lambda c:(len(c),c))
    print('80 active',public_probe(ordered,256),public_probe(ordered,65536),
          experiment(ordered,set(range(1,37)),w80))
~~~
