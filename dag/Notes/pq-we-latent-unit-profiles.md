---
title: Existential witness projection through forced literals before binary inner-product WE
refs: [definition:WE_CircuitSAT, note:pq-we-split-witness-abe, theorem:AdvancedEncryption.WE.IPE.forced_literal_extension_iff]
tags: [witness-encryption, circuit-sat, predicate-encryption, preprocessing]
---

A binary zero-inner-product scheme can serve many original witnesses with the same pair of entries. This note gives two exact ways to existentially project witness bits, including bits occurring on opposite sides of the intended cut. It builds on the [rectangle compiler in #88](https://github.com/MachinaIO/SigabaPark/pull/88) and the [counting and ranking procedures in #91](https://github.com/MachinaIO/SigabaPark/pull/91). The underlying cryptographic interface and ordinary decision-LWE premise remain those of the AFV route. Increasing the predicate dimension changes the quantitative requirements.

### Group ciphertext attributes before encryption

Suppose the cut compiler represents a violation by a rectangle i whose hit bit on either side is the OR of several subclause failures. Pick hidden attribute-side variables with at most one in each local clause and in each attribute-side subclause. Multiple hidden variables may occur in the same *rectangle*, through different subclauses. Fix the remaining attribute bits z. Purely visible failing subclauses require the corresponding key hit bits to vanish. The local clauses of each hidden bit h give its allowable branches (zero, one or both bit values). Reject the bucket if any bit has no allowed branch or a visible local clause fails. To index only nonempty buckets, resolve h out of its local clauses. These local eliminations do not couple the selected hidden bits.

For each allowed value b, let A_b be the set of rectangle indices for which an h-dependent subclause fails at that value. The block can pass if some allowed A_b is disjoint from the set of key hits. For a single branch its failure is a disjunction of singleton hits. For two branches it is a disjunction of singleton hits on A_0 intersect A_1 and pair hits v_i AND v_j with i in A_0 minus A_1, j in A_1 minus A_0. The latter need only be available where h occurs positively in some subclause at i and negatively at j, in either order. These pairs form one public feature dictionary for all buckets. Emit the original singleton key bits and the extra binary conjunctions. A ciphertext attribute marks all its rejecting terms. Taking the union of the terms over blocks is exact because their allowed branch choices are independent; shared rectangle indices introduce no cross-block constraint once the key vector is fixed. An inner product modulo a prime larger than the dictionary size detects whether any marked term holds. This construction samples one key for the whole lifted vector, with no need to disclose separate keys for its coordinates. Each original satisfying witness decrypts using its visible projection.

On the residual 80-active-input, 355-clause control of #91 (after sibling simplification), projecting ten of the 36 attribute-side bits takes the domain from 1,487,594,368 entries in dimension 132 to 9,993,984 entries in dimension 314. The ciphertext-vector count (1+p)C falls from 197,850,050,944 to 3,148,104,960. The key-side local domain is unchanged. The full AFV ciphertext contains one scalar plus m times this many vector residues per table, summed over entries as C + m(1+p)C. On the 300-clause control, projecting nine of 39 attribute-side bits reduces 8,052,145,024 entries in dimension 113 to 130,048,192 in dimension 136. This comparison starts from globally projected local assignments, prior to #91's block-dominance pass.

### Remove a hidden binary implication system on either side

Choose hidden variables H. Each clause must either have no hidden literal, have exactly one hidden literal u and a visible disjunction B, or belong entirely to a static binary formula on H. Treat units as empty-guard demands. The clause B OR u demands u exactly when B fails. A simple selection rule forbids co-selecting two distinct variables from any clause of width greater than two. It can still select adjacent variables in static binary clauses. Normalize duplicates and tautologies first.

Build the usual implication graph of the static binary clauses and its reflexive transitive closure R. A mutually reachable complementary pair proves public NO. Otherwise retain every visible-only clause. For all demand pairs (u,B),(v,C), including a pair with itself, emit B OR C if R(u,neg v); drop tautologies, duplicates and supersets. The 2-SAT graph and its contrapositive symmetry are classical. See [Aspvall, Plass and Tarjan](https://mathweb.ucsd.edu/~sbuss/CourseWeb/Math268_2007WS/2SAT.pdf).

To see exactness, fix the visible bits. A compatible demand set has a consistent reachability closure: if demands u,v reach complementary literals, contraposition makes u reach neg v. Starting from that closure, orient each unset variable. If adding d would make its own cone inconsistent, d reaches neg d. If its cone conflicted with an old chosen literal, closure and contraposition would already have chosen neg d. At least one orientation is possible since d and neg d are not mutually reachable. Conversely a consistent closed assignment excludes every conflicting demand pair. The Lean theorem forced_literal_extension_iff proves this extension result for arbitrary literal types, a complement involution, any such relation R and any finite list of variables. Applied to all hidden variables it gives a genuine satisfying extension, including on disconnected and unconstrained components. The reference reconstructs and checks extensions. On a chain of 64 hidden equalities with the two endpoints separately forced to opposite values by visible conditions, all hidden bits disappear and one visible binary clause remains.

The residual CNF may be considerably larger. The prototype makes at most ten rounds, screens at 3,500 distinct candidate clauses before final subsumption, and accepts up to 3,000 after subsumption. It retries with successively shorter prefixes of the chosen hidden set. It can stop at any completed round. Each round still scans guards and reachability pairs, even when many emitted clauses coincide. Those operations and all failed attempts require finite work budgets in a tape-machine submission. The graph formulation allows a single batch across a cyclic hidden implication graph. For independent hidden variables the rule specializes to simultaneous Davis–Putnam resolution with controlled clause expansion.

After projection, recompute the star cover and the cut. A given original witness restricts through all the rounds. Every residual witness lifts in reverse order, so false statements remain false at each cryptographic branch. Reuse the selected-key / same-attribute hybrid of #88 with the new counts. In particular, the projecting step does not add an exponential search to decryption.

### Counts and public decision controls

Starting from #91's globally preprocessed CNF, the following counts use public, deliberately asymmetric cuts and a local frontier cap of 1,800. If necessary the ranker moves omitted local checks into up to two additional predicate coordinates. This makes counts exact for the candidate domains actually enumerated. They can include tuples rejected by the guard coordinates.

| Original input | Projection rounds | Active variables / clauses | Predicate dimension | Keys | Ciphertexts |
|---|---:|---:|---:|---:|---:|
| 128 active, 300 clauses, seed 851 | 3 | 53 / 844 | 426 | 531791744 | 2752512 |
| same | 6 | 48 / 2472 | 1076 | 209012224 | 458752 |
| 80 active, 355 clauses, seed 655 | 3 | 55 / 2594 | 886 | 216647840 | 2226176 |
| 128 active, 540 clauses, seed 851 | 4 | 88 / 2623 | 1078 | 50848670941184 | 43689009152 |

Relative to #91's compressed 300-clause row, the six-round result reduces the ciphertext count by a factor of 8,672 and the key count by 355, rounded. The structural proxy 2K+(1+p)C falls from 601,776,556,152 to 912,100,352 (factor 660). At illustrative m=524288 this still means 259,038,068,015,104 ciphertext residues and 219,165,201,793,024 short key coordinates. The larger dimension consumes noise and modulus headroom. A uniform public cap C<=458752 would give a single-challenge squared-advantage floor of 166 bits for the 128-bit target before reduction time, sampling error and key-query costs. A branch satisfying that cap still needs certified hardness, width, sampler, and work bounds.

For the dense 540-clause seed-851 control which exceeded the old 256-node search cap, the third residual is publicly SAT in 215 nodes of the same unit-propagating solver. Its equivalent original sorted CNF exhausted 1,280 nodes. Nodes on different formulas have different costs. On this run a portfolio using at most 256 search nodes on the original and on each of up to four successive residuals consumed 0.80 CPU seconds including projection, compared with 0.67 seconds for the inconclusive 1,280-node original probe. Exact public YES permits the bit itself to be sent; exact NO permits a fixed constant. For five further consecutive seeds, 852, 853, 855 and 856 were solved by both approaches, and 854 exhausted both budgets. These observations do not establish average-case hardness or a universal speedup.

### Rankable local domains on the unresolved dense control

On seed 854 four rounds leave 86 variables and 2,860 clauses. To avoid a large local counting frontier, build a bounded decision tree separately for each side. Propagate units, cut a branch on contradiction, and otherwise branch on a variable of greatest literal frequency. At the depth limit, greedily keep clauses whose variable–clause incidence graph is a forest. A clause can be added when its variables belong to distinct current components. Each surviving tree leaf describes a superset of the true local models. If any leaf omitted clauses, add one binary invalid-local coordinate for that side as in #91. A satisfying witness follows its unique branch. An accepting cryptographic pair must satisfy the full local tests. This leaves the proof on NO instances intact.

Count a forest by passing two integer counts per variable toward a chosen root, one count for each bit value. If the parent literal already satisfies a child clause, multiply the sums of the child variables' counts. Otherwise subtract the product for the single all-falsifying pattern. Multiply over child clauses, sum the two root counts and multiply over components, including isolated variables. Conditioning forest variables can only delete edges. Thus inside a leaf, fixing each next bit and recounting the remaining forest gives exact disjoint interval lengths for rank and inverse rank. Above the leaves use the two subtree counts. This avoids materializing the domain; directory size, conditional recounts, sorting clauses and enumerating all cryptographic entries remain costs. Explicit unit choices that are forced on a path are inserted by the inverse rank operation.

We chose a 40-variable attribute side by a deterministic 1,500-proposal cut search. The score treats clause satisfaction fractions as independent for ordering cuts only. The table uses exact candidate-domain counts. Both sides reserve their invalid-local coordinate.

| Local branch depth | AFV dimension | Ciphertexts | Keys | 2K+(1+p)C |
|---:|---:|---:|---:|---:|
| 9 | 831 | 2338081130 | 179476742856 | 2304236985872 |
| 13 | 831 | 317771780 | 28307281896 | 321000684752 |
| 17 | 831 | 79437951 | 8965806142 | 84023987516 |

The depth-17 single-control run, including projection, cut selection, both directories and selected rank checks, took 9.07 s elapsed with 240,884 KiB peak RSS on this host. No AFV keys or ciphertexts were generated in this measurement. More public search is highly competitive here: raising the original-formula DPLL cap returned SAT in 4,818 nodes (2.56 CPU s). The held-out instance demonstrates both a cryptographic fallback when the short probe fails and why a more generous public probe can be preferable. No example here establishes that the cryptographic path is the cheapest possible decision procedure.

### A false statement with a checked refutation

Security quantifies over false statements. Generate uniform signed ternary clauses without planting a witness. Among the two seeds 1201 and 1202 tried at 128 variables and 560 clauses, seed 1202 is UNSAT. The reference emits a 3,753-node binary refutation tree and checks it against the original clauses in a separate routine. At each node every recorded unit step must have exactly one unset literal in a cited unsatisfied clause. A contradiction leaf cites a clause with all literals false. A split must cover both values of a previously unset variable. These checks prove global rejection without using the projection compiler to classify the instance. The original 1,280-node probe and all three 256-node residual probes exhaust their budgets. Projection stops at 88 variables and 2,970 clauses. Both side domains are nonempty.

| Local branch depth | Dimension | Ciphertexts | Keys |
|---|---:|---:|---:|
| 13 | 672 | 446452171 | 82628466415 |
| 17 | 672 | 97128514 | 27454170802 |

For a separate practical comparison, pycosat 0.6.6 returned SAT on the dense seed-854 control in 1.49 ms and UNSAT on seed 1202 in 2.56 ms in a local call per instance. We checked the returned SAT model, and the independent tree above certifies the NO answer. An encryption implementation can accept only checked witnesses/refutations within an explicit public generation and checking budget, then use an independently bounded WE fallback. These timings underscore why search budgets and solver choice must be named when evaluating these small controls.

### Reproduction and verification boundary

Run Python 3 with the two listings below and in the [pinned #91 note](https://github.com/MachinaIO/SigabaPark/blob/29b7f29db2ea0554e5ea76db6cc5533f3180b1cf/dag/Notes/pq-we-block-dominance.md). Save the Python listing from #91 as profiles.py and this listing as latent.py. Run `python latent.py profiles.py`. The inputs marked 80 active use only those inputs of the 128-bit relation. All measurement formulas are small enough for the circuit gate cap: a three-literal OR takes at most three NANDs from both input polarities and the conjunction costs two per extra clause, with at most 128 input negations. Symbolically projected clauses are preprocessing data; their larger circuit expansions need not fit back into the original statement.

The tests exhaust the visible/hidden truth tables on 200 small bucket instances and check projected model images and reconstructed extensions on 160 small joint-elimination instances. Another 100 small local formulas check the forest domain, count, rank and inverse rank, including its relaxation boundary. The large runs reconstruct satisfying assignments through all completed projection rounds and compare selected local ranks. Both dense YES and unplanted NO controls were also compiled to actual 4,096-gate input lists and evaluated on sampled assignments. The Lean proof covers the demand-extension criterion. The circuit compiler, resource limits, concrete quantum security and full tape-machine cost are open.

~~~python
from itertools import product, combinations_with_replacement
from collections import Counter, defaultdict
from math import log2
import runpy
import sys

# Pass the extracted Python listing of PR 91 as the sole command-line argument.
m=runpy.run_path(sys.argv[1])


def plan(rows,left,n):
    local,_,cover=m['compile_cnf'](n,rows,left)
    supports=[set(map(abs,sub)) for pair in cover for sub in pair[0]]
    forbidden={v:set() for v in left}
    for group in supports+[set(map(abs,c)) for c in local[0]]:
        for v in group:forbidden[v]|=group-{v}
    def pairs(v):
        a={i for i,(subs,_) in enumerate(cover) if any(v in sub for sub in subs)}
        b={i for i,(subs,_) in enumerate(cover) if any(-v in sub for sub in subs)}
        return {tuple(sorted((i,j))) for i in a for j in b if i!=j}
    new={v:pairs(v) for v in left};hidden=[];allowed=set(left)
    while allowed:
        v=min(allowed,key=lambda v:((len(forbidden[v]&allowed)+1)*(len(new[v])+1),v))
        hidden.append(v);allowed-={v}|forbidden[v]
    return hidden,local,cover,new

def forget(rows,vs):
    cs={frozenset(c) for c in rows}
    for v in vs:
        A=[c for c in cs if v in c];B=[c for c in cs if -v in c]
        cs-=set(A)|set(B)
        for a in A:
            for b in B:
                u=(a|b)-{v,-v}
                if not any(-j in u for j in u):cs.add(u)
    return m['simplify'](cs)

def compile_bucket(local,cover,hidden,extra,z):
    hs=set(hidden);parts={h:[] for h in [None]+list(hidden)}
    for i,(subs,_) in enumerate(cover):
        for sub in subs:
            owners=set(map(abs,sub))&hs
            assert len(owners)<=1
            parts[next(iter(owners),None)].append((i,sub))
    def active(h,x):
        return {i for i,sub in parts[h] if not m['satisfies']([sub],x)}
    terms={(i,) for i in active(None,z)}
    if any(not ({abs(a) for a in c}&hs) and not m['satisfies']([c],z) for c in local):
        return None
    for h in hidden:
        clauses=[c for c in local if any(abs(a)==h for a in c)]
        assert all(sum(v in hs for v in set(map(abs,c)))==1 for c in clauses)
        variants=[]
        for b in (0,1):
            bit=1<<(h-1)
            x=(z&~bit)|(b*bit)
            if m['satisfies'](clauses,x):
                variants.append(active(h,x))
        if not variants:return None
        if len(variants)==1:
            terms.update((i,) for i in variants[0])
        else:
            A,B=variants;terms.update((i,) for i in A&B)
            terms.update(tuple(sorted((i,j))) for i in A-B for j in B-A)
    assert all(len(t)==1 or t in extra for t in terms)
    return terms

def test():
    from random import Random
    g=Random(905)
    for _ in range(200):
        n=g.randrange(2,9)
        rows=[list(dict.fromkeys(g.choice((-1,1))*g.randint(1,n) for _ in range(g.randint(1,4)))) for _ in range(g.randrange(1,16))]
        rows=[c for c in rows if not any(-a in c for a in c)]
        left={i for i in range(1,n+1) if g.randrange(2)}
        hidden,local,cover,new=plan(rows,left,n);hs=set(hidden)
        extra=set().union(*(new[h] for h in hidden))
        projected=forget(local[0],hidden)
        for z in range(1<<n):
            if any(z>>(h-1)&1 for h in hidden):continue
            terms=compile_bucket(local[0],cover,hidden,extra,z)
            assert (terms is not None)==m['satisfies'](projected,z)
            key=[any(not m['satisfies']([s],z) for s in subs) for _,subs in cover]
            accepts=terms is not None and m['satisfies'](local[1],z) and not any(all(key[i] for i in t) for t in terms)
            actual=any(m['satisfies'](rows,z|sum(b<<(h-1) for h,b in zip(hidden,bs))) for bs in product((0,1),repeat=len(hidden)))
            assert accepts==actual

def stats(F,L,n):
    r,_,_=m['project'](F,n,8,0);rows,left,vs=m['shrink'](r,L,n)
    hidden,loc,cover,new=plan(rows,left,len(vs))
    for count in sorted({0,len(hidden)//2,len(hidden)}):
        h=hidden[:count];rest=left-set(h);extra=set().union(*(new[v] for v in h))
        local=forget(loc[0],h);basis=[({v},[0,1<<(v-1)]) for v in sorted(rest)]
        num,states,convert=m['index'](basis,local,rest)
        # Check representative buckets by rank at both ends and in the middle.
        for j in {0,num//2,num-1} if num else set():
            z=convert(j,True);assert convert(z,False)==j
            compile_bucket(loc[0],cover,h,extra,z)
        print(len(vs),len(left),count,len(cover),len(extra),num,states,num*(1+len(cover)+len(extra)),flush=True)

def choose(rows,V):
    adj={v:set() for v in V}
    occ=Counter(abs(a) for c in rows for a in c)
    for c in rows:
        if len(c)<=2:continue
        for a in c:adj[abs(a)].update(abs(b) for b in c if abs(a)!=abs(b))
    todo=set(V);out=[]
    while todo:
        v=min(todo,key=lambda v:(len(adj[v]&todo),occ[v],v))
        out.append(v);todo-={v}|adj[v]
    return out

def eliminate(rows,hidden):
    hidden=set(hidden); graph={i:set() for v in hidden for i in (v,-v)}
    demands=[];keep=set()
    for c in rows:
        latent=[a for a in c if abs(a) in hidden]
        visible=frozenset(a for a in c if abs(a) not in hidden)
        if not latent:keep.add(visible)
        elif len(latent)==1:demands.append((latent[0],visible))
        elif len(latent)==2 and not visible:
            a,b=latent;graph[-a].add(b);graph[-b].add(a)
        else:raise ValueError('guarded non-unit or nonbinary hidden constraint')
    reach={}
    for a in graph:
        stack=[a];seen={a}
        while stack:
            for b in graph[stack.pop()]-seen:seen.add(b);stack.append(b)
        reach[a]=seen
    if any(-a in reach[a] and a in reach[-a] for a in hidden):return {frozenset()}
    for (a,c),(b,d) in combinations_with_replacement(demands,2):
        if -b not in reach[a]:continue
        k=c|d
        if not any(-j in k for j in k):keep.add(k)
        if len(keep)>3500:raise OverflowError
    return m['simplify'](keep)

def tests():
    from random import Random
    g=Random(319)
    for t in range(160):
        n=g.randint(1,8);F=[]
        for j in range(g.randrange(24)):
            vs=g.sample(range(1,n+1),g.randrange(min(4,n)+1))
            F.append(tuple(v*g.choice((-1,1)) for v in vs))
        h=choose(F,set(range(1,n+1)));out=eliminate(F,h)
        hm=sum(1<<(v-1) for v in h)
        image={x&~hm for x in range(1<<n) if m['satisfies'](F,x)}
        for x in range(1<<n):
            if not x&hm:assert (lift(F,h,x) is not None)==(x in image)
        assert image=={x for x in range(1<<n) if not x&hm and m['satisfies'](out,x)}

def lift(rows,hidden,x):
    H=set(hidden)
    edges={a:set() for h in H for a in (-h,h)}
    forced=set()
    for c in rows:
        T=[a for a in c if abs(a) in H];E=[a for a in c if abs(a) not in H]
        if any(bool(x>>(abs(a)-1)&1)==(a>0) for a in E):continue
        if not T:return None
        if len(T)==1:forced.add(T[0])
        elif len(T)==2 and not E:
            a,b=T;edges[-a].add(b);edges[-b].add(a)
        else:raise ValueError
    def closure(seeds):
        known=set(seeds);stack=list(known)
        while stack:
            for b in edges[stack.pop()]-known:known.add(b);stack.append(b)
        return known
    def bad(U):return any(-a in U for a in U)
    A=closure(forced)
    if bad(A):return None
    for h in sorted(H):
        if h in A or -h in A:continue
        for a in (h,-h):
            cand=A|closure({a})
            if not bad(cand):A=cand;break
        else:return None
    ans=(x&~sum(1<<(v-1) for v in H))|sum(1<<(a-1) for a in A if a>0)
    assert m['satisfies'](rows,ans)
    return ans

def chain():
    # Hidden equivalences, two gated unit requests and a satisfiable base.
    n=66;hidden=list(range(3,n+1))
    rows=[(-v,v+1) for v in range(3,n)]+[(v,-v-1) for v in range(3,n)]
    rows += [(1,3),(2,-n)]
    out=eliminate(rows,hidden);assert out=={frozenset((1,2))}
    for x in range(4):assert (lift(rows,hidden,x) is not None)==bool(x)
    impossible=[(3,4),(3,-4),(-3,4),(-3,-4)]
    assert eliminate(impossible,[3,4])=={frozenset()}
    assert lift(impossible,[3,4],0) is None

def massage(F,climit=3000,rounds=10):
    F=set(map(frozenset,F))
    for step in range(rounds):
        V={abs(a) for c in F for a in c};hs=choose(F,V)
        pos=defaultdict(int)
        for c in F:
            for a in c:pos[a]+=1
        # Small steps limit backtracking when symbolic elimination would grow.
        hs.sort(key=lambda v:(pos[v]*pos[-v]-pos[v]-pos[-v],v))
        group=hs.copy()
        while group:
                # Use the exact reach-based materializer below with a pre-simplification cap.
            try:G=eliminate(F,group)
            except OverflowError:G=None
            if G is not None and len(G)<=climit:break
            group=group[:len(group)//2]
        if not group:break
        F=G
        yield F,group



def counts(rr,n):
    vs=sorted({abs(a) for c in rr for a in c});p0=len(rr)
    left=set(vs[:max(0,round((len(vs)-log2(max(1,p0/2)))/2))])
    rows,l,vs=m['shrink'](rr,left,n)
    loc,_,cover=m['compile_cnf'](len(vs),rows,l);dim=len(cover);tot=[]
    for side,cs in zip((l,set(range(1,len(vs)+1))-l),loc):
        bs=[({v},[0,1<<(v-1)]) for v in sorted(side)]
        whole=sorted(cs,key=lambda c:(len(c),tuple(sorted(c))));keep=whole
        while True:
            try:cnt,st,_=m['index'](bs,keep,side,limit=1800);break
            except OverflowError:keep=keep[:len(keep)//2]
        dim+=int(len(keep)<len(whole));tot.append(cnt)
    return len(l),dim,*tot,2*tot[1]+(1+dim)*tot[0]

if __name__=='__main__':
    test();tests();chain()
    for n,mc,seed in ((128,300,851),(80,355,655),(128,540,851)):
        w,F=m['planted'](n,mc,seed)
        if n==80:F,_=m['sibling_closure'](F)
        L=(m['improve'](F)|{12,76,36})-{14,112} if mc==300 else set(range(1,37))
        if mc!=540:stats(F,L,n)
        r,_,_=m['project'](F,n,8,0)
        trace=[]
        for step,(rr,h) in enumerate(massage(r)):
            trace.append((r,h))
            visible={abs(a) for c in rr for a in c}
            z=w&sum(1<<(v-1) for v in visible)
            assert m['satisfies'](rr,z)
            for old,hid in reversed(trace):
                z=lift(old,hid,z);assert z is not None
            print(n,mc,step+1,len(visible),len(rr),counts(rr,n),flush=True)
            ordered=sorted((tuple(sorted(c)) for c in rr),key=lambda c:(len(c),c))
            print('residual decision',m['public_probe'](ordered,256))
            r=rr


from random import Random
from math import prod
from math import log2
from random import Random
def fit(rows,attr):
    # Independent-clause fractions serve as a cut-ordering heuristic only.
    n=max(abs(a) for c in rows for a in c);full=(1<<n)-1
    masks=[sum(1<<(v-1) for v in set(map(abs,c))) for c in rows]
    weights=[log2(1-2.0**-len(c)) for c in rows]
    def score(x):
        y=full^x;A=attr;K=n-attr;cross=0
        for u,lg in zip(masks,weights):
            if u&x==0:K+=lg
            elif u&y==0:A+=lg
            else:cross+=1
        return 2**(1+K)+(1+cross)*2**A
    x=(1<<attr)-1;best=score(x);g=Random(832)
    for _ in range(1500):
        a,b=g.sample(range(n),2)
        if ((x>>a)^(x>>b))&1:
            u=x^(1<<a)^(1<<b);val=score(u)
            if val<best:x,best=u,val
    return {v+1 for v in range(n) if x>>v&1}

from collections import Counter
from math import prod

def restrict(cs,a):
    return [tuple(v for v in c if v!=-a) for c in cs if a not in c]

def forest(cs,vs):
    parent={v:v for v in vs}
    def root(v):
        while v!=parent[v]:
            parent[v]=parent[parent[v]];v=parent[v]
        return v
    keep=[]
    for c in sorted(cs,key=lambda c:(len(c),tuple(sorted(c)))):
        rs=[root(abs(l)) for l in c]
        if len(set(rs))!=len(rs):continue
        keep.append(c)
        for r in rs[1:]:parent[r]=rs[0]
    return keep

def treecount(cs,vs):
    if any(not c for c in cs):return 0
    touching={v:[] for v in vs};seen=set()
    for i,c in enumerate(cs):
        for a in c:touching[abs(a)].append((i,a))
    def message(v,back):
        seen.add(v);out=[1,1]
        for i,a in touching[v]:
            if i==back:continue
            total=fail=1
            for b in cs[i]:
                if abs(b)==v:continue
                c0,c1=message(abs(b),i)
                total*=c0+c1;fail*=c0 if b>0 else c1
            out[a>0]*=total;out[a<0]*=total-fail
        return out
    count=1
    for v in sorted(vs):
        if v not in seen:count*=sum(message(v,None))
    return count

def build_tree(cs,vs,depth):
    forced=0;vs=set(vs)
    while cs:
        c=min(cs,key=len)
        if not c:return (0,False,None)
        if len(c)>1:break
        a=c[0];vs.remove(abs(a));cs=restrict(cs,a)
        if a>0:forced|=1<<(a-1)
    if not depth or not cs:
        fs=forest(cs,vs)
        return treecount(fs,vs),len(fs)!=len(cs),(forced,vs,fs)
    cnt=Counter(abs(a) for c in cs for a in c)
    v=max(cnt,key=lambda v:(cnt[v],-v))
    branches=[build_tree(restrict(cs,a),vs-{v},depth-1) for a in (-v,v)]
    return sum(ch[0] for ch in branches),any(ch[1] for ch in branches),(forced,v,branches)

def address(tree,x,unrank):
    count,_,node=tree
    if unrank and not 0<=x<count:raise ValueError
    forced,obj,data=node
    if isinstance(obj,int):
        v=obj;zero=data[0][0];b=int(x>=zero) if unrank else (x>>(v-1))&1
        if unrank:return forced|(b<<(v-1))|address(data[b],x-b*zero,True)
        return b*zero+address(data[b],x,False)
    vs=set(obj);cs=data;rank=0;y=forced
    for v in sorted(obj):
        vs.remove(v)
        z=restrict(cs,-v);zero=treecount(z,vs)
        b=int(x>=zero) if unrank else (x>>(v-1))&1
        if b:
            if unrank:x-=zero
            rank+=zero;y|=1<<(v-1);cs=restrict(cs,v)
        else:cs=z
    return y if unrank else rank

def forest_size(rows,side,depth):
    tree=build_tree(rows,side,depth)
    for j in {0,tree[0]//2,tree[0]-1} if tree[0] else ():
        assert address(tree,address(tree,j,True),False)==j
    return tree[:2]

def forest_test():
    g=Random(833)
    for _ in range(100):
        n=g.randint(1,8);vs=set(range(1,n+1))
        clauses=[tuple(a*g.choice((-1,1)) for a in g.sample(sorted(vs),g.randrange(min(4,n)+1)))
                 for _ in range(g.randrange(15))]
        tree=build_tree(clauses,vs,g.randrange(4))
        domain={address(tree,j,True) for j in range(tree[0])}
        assert len(domain)==tree[0]
        assert all(address(tree,address(tree,j,True),False)==j for j in range(tree[0]))
        exact={x for x in range(1<<n) if m['satisfies'](clauses,x)}
        assert exact<=domain and (tree[1] or exact==domain)
        if not any(not c for c in clauses):
            f=forest(clauses,vs)
            assert treecount(f,vs)==sum(m['satisfies'](f,x) for x in range(1<<n))

if __name__=='__main__':
    from time import process_time
    forest_test()
    for seed in range(851,857):
        w,F=m['planted'](128,540,seed)
        def order(rows):return sorted((tuple(sorted(c)) for c in rows),key=lambda c:(len(c),c))
        t=process_time();baseline=m['public_probe'](order(F),1280);elapsed=process_time()-t
        t=process_time();stages=[m['public_probe'](order(F),256)]
        if stages[-1][0] is None:
            r,_,_=m['project'](F,128,8,0)
            for rr,h in massage(r,rounds=4):
                stages.append(m['public_probe'](order(rr),256))
                if stages[-1][0] is not None:break
        print('probe',seed,baseline,elapsed,stages,process_time()-t,flush=True)
        if seed==854:
            assert len(stages)==5 and stages[-1][0] is None
            print('larger original probe',m['public_probe'](order(F),65536))
            rows,_,vs=m['shrink'](rr,set(),128);left=fit(rows,40)
            loc,_,cover=m['compile_cnf'](len(vs),rows,left)
            for depth in (9,13,17):
                results=[forest_size(cs,side,depth) for cs,side in
                         zip(loc,(left,set(range(1,len(vs)+1))-left))]
                C,K=[count for count,_ in results]
                p=len(cover)+sum(guard for _,guard in results)
                print('forest',depth,p,C,K,2*K+(1+p)*C,flush=True)

def generate(n,num,seed):
    g=Random(seed)
    return [tuple(v*g.choice((-1,1)) for v in g.sample(range(1,n+1),3)) for _ in range(num)]

def refute(F,limit):
    used=0
    def sub(rows,a):
        return [(i,c-{-a}) for i,c in rows if a not in c]
    def visit(rows):
        nonlocal used
        used+=1
        if used>limit:raise OverflowError
        units=[]
        while rows:
            i,c=min(rows,key=lambda ic:len(ic[1]))
            if not c:return units,i
            if len(c)>1:break
            units.append(i);rows=sub(rows,next(iter(c)))
        if not rows:raise ValueError('satisfying branch')
        freq=Counter(a for _,c in rows for a in c)
        a=max(freq,key=lambda a:(freq[a]+freq[-a],freq[a],a))
        return units,(a,visit(sub(rows,a)),visit(sub(rows,-a)))
    proof=visit([(i,frozenset(c)) for i,c in enumerate(F)])
    return proof,used

def check_refutation(F,proof):
    nodes=0
    def visit(node,assigned):
        nonlocal nodes
        nodes+=1
        units,end=node
        for i in units:
            c=F[i]
            assert not any(a in assigned for a in c)
            unassigned=[a for a in c if -a not in assigned]
            assert len(unassigned)==1
            assigned.add(unassigned[0])
        if isinstance(end,int):
            assert all(-a in assigned for a in F[end]);return
        a,l,r=end
        assert a and a not in assigned and -a not in assigned
        visit(l,assigned|{a});visit(r,assigned|{-a})
    visit(proof,set())
    return nodes

def raw_ternary(rows,n=128,gates=4096):
    prog=[]
    def nand(i,j):
        prog.append((i,j));return n+len(prog)
    neg={v:nand(v,v) for v in range(1,n+1)}
    def complement(a):return neg[a] if a>0 else -a
    acc=0
    for a,b,c in rows:
        t=nand(complement(a),complement(b))
        clause=nand(nand(t,t),complement(c))
        t=nand(acc,clause);acc=nand(t,t)
    back=nand(acc,acc);assert len(prog)<gates
    while len(prog)+1<gates:nand(0,0)
    nand(back,back)
    return prog

if __name__=='__main__':
    F=generate(128,560,1202)
    proof,nodes=refute(F,100000)
    assert check_refutation(F,proof)==nodes
    print('checked refutation nodes',nodes)
    for cs in (F,m['planted'](128,540,854)[1]):
        prog=raw_ternary(cs)
        rng=Random(349)
        for x in [m['planted'](128,540,854)[0]]+[rng.getrandbits(128) for _ in range(16)]:
            wires=[True]+[bool(x>>j&1) for j in range(128)]
            for i,j in prog:wires.append(not (wires[i] and wires[j]))
            assert wires[-1]==m['satisfies'](cs,x)
    print('original NO probe',m['public_probe'](order(F),1280))
    r,_,_=m['project'](F,128,8,0)
    for rr,h in massage(r,rounds=4):
        print('NO round',len(rr),m['public_probe'](order(rr),256),flush=True)
    rows,_,vs=m['shrink'](rr,set(),128);left=fit(rows,len(vs)//2-3)
    loc,_,cover=m['compile_cnf'](len(vs),rows,left)
    for depth in (13,17):
        results=[forest_size(cs,s,depth) for cs,s in zip(loc,(left,set(range(1,len(vs)+1))-left))]
        print('NO domains',depth,len(cover)+sum(t[1] for t in results),results)
~~~
