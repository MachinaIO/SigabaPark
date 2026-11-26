---
title: Reusing local certificates and eliminating repeated encryptions in separator WE
refs: [definition:WE_CircuitSAT, theorem:AdvancedEncryption.WE.Separator.support_insert, theorem:AdvancedEncryption.WE.Separator.template901_counts]
tags: [witness-encryption, circuit-sat, compilation, complexity]
---

The separator construction of [PR 102](https://github.com/MachinaIO/SigabaPark/pull/102) can encrypt many occurrences of the same local predicate. Compile the access condition on the *distinct* local predicates before emitting any ciphertext. This can shorten every honest algorithm without changing the hardness assumption of a chosen one-bit leaf backend. In the examples below it also shortens the matrix ciphertext **at the same lattice scale**. The compiler handles arbitrary NAND circuits by using a bounded attempt and a monolithic fallback. Savings are instance-dependent.

### Local witness maps

Use consecutive bags with all crossing wires in the separators, as in PR 102. Fix both endpoint states for each candidate transition. Evaluate the local NANDs symbolically using constants, local private inputs, signed references and two-input AND nodes. Enforce equality to every requested output and, in the final bag, the asserted circuit output. Inconsistent pins give constant false. Fold constants, equal inputs, complements and double negations. Share nodes with identical ordered operand pairs. Retain only nodes feeding the result. Scan in dependency order and assign dense indices to nodes and to the surviving private inputs. The canonical key is the full resulting program and the signed output reference, compared by structural equality. Different presentations of equivalent circuits can remain distinct.

The occurrence also records where to read each surviving private input. Its witness becomes a witness for the canonical program by projection. Conversely, put the canonical bits back in the recorded positions and fill unused private inputs arbitrarily. Gate induction proves exact preservation in both directions, also for internal outputs fixed by a boundary. Thus one valid certificate for a type suffices at every occurrence of that type. The boundary values are already fixed in its predicate. The interval property ensures local extensions on a selected path glue to one circuit witness. Dropping boundary checks or identifying predicates solely by sampling their outputs would invalidate the argument.

### Compile the access condition

A label is a canonical nonconstant predicate. Omit false edges and assign the empty requirement to true edges. Along a path collect its set of labels. The accepting condition is the monotone disjunction over realizable paths of the conjunctions of their required labels. Enc computes these requirements from syntax; it never asks whether an opaque predicate has a witness. Start the source with the empty support. At every edge add its label to each incoming support and insert the result at the destination. Discard a new support containing an old one; otherwise delete all its supersets. The Lean theorem proves that this operation preserves feasibility for every available label set. Union with the same edge label preserves inclusion, so the invariant holds through all layers. This is the minimal-path-set representation of a monotone function; the application here needs witness transport to justify the labels. [Marichal, Structure functions and minimal path sets](https://orbilu.uni.lu/handle/10993/23215).

The terminal antichain gives a DNF. Its minimal hitting sets give a dual CNF: a set of available labels contains a term iff it meets every minimal hitting set. For the reverse implication, if no term is contained, the unavailable labels hit every term and contain a minimal hitting set. Empty families and empty terms give the appropriate constants. The prototype also tries both positive Shannon factorizations with a pivot x: if f0 and f1 are its restrictions then f0 implies f1, and either f0 OR (x AND f1) or f1 AND (x OR f0) computes f. The implementation chooses the smallest completed tree among the candidates it found, counting leaf occurrences. It does not optimize globally over all monotone formulas.

For AND, choose uniform independent bit shares except the last and fix their XOR to the payload. For OR, recursively encrypt the same payload on each branch using independent coins. A leaf encrypts one bit under the canonical predicate. True constants publish the bit; false constants publish zero. A holder of an original witness evaluates its trace once and obtains a dictionary of canonical certificates from its path. This available label set satisfies the tree. Use all AND children and one OR child supported by the dictionary, passing the matching canonical witness to each selected leaf Dec. No search for a witness or global feasible path is necessary. The implementation checks dictionary entries by evaluating their canonical programs in its tests. For a false statement the set of all satisfiable labels makes the formula false. At a false OR all branches are false; hybridize over branches. At a false AND embed the challenge in one false child and take all other shares uniformly. This gives the usual conditional false-statement security with a sum of the challenged leaf advantages and simulation costs. Correctness costs at most the sum of errors for the decryptions actually used. These classical loops preserve quantum postprocessing security if the underlying games hold for quantum distinguishers; the transformations introduce no new computational premise.

### Different predicates can also share a certificate

For two types i,j accept a directed implication only with a witness translator valid on every accepting witness for i. The prototype automatically finds j by descending through positive ANDs of i, stopping at complemented nodes. If a resulting subexpression canonicalizes to j, project the source witness according to that subexpression's ports. Keep only strict edges; proper subexpressions shrink in size. Chaining projections is polynomial for this implementation. Every original accepted certificate can now provide all certificates below it.

Propagate the *closures* of path supports under this implication order; closure of a union is the union of the closures. Domination of closures is sound, since the set of globally satisfiable labels and the dictionary after transport are both downward closed. At the terminal reduce each closed support to its maximal generators before building the formula. A downward-closed dictionary contains those generators iff it contains every member of the support. In particular two separately supplied witnesses for conjuncts of a predicate do not certify their conjunction on one private input. The implication checker only descends from a witness already satisfying the joint predicate.

### Residual repetitions

There is a computational option for a type occurring d times after factoring, with independent outer sharing and seed coins. Instead of d single-bit leaf ciphertexts, encrypt a fresh k-bit seed under the type, bitwise. Expand the seed to d pseudorandom bits and publish the vector of d leaf payloads masked by the expansion. A recipient decrypts the seed once per required type, then obtains the needed positions. Across all types the expensive leaf count becomes at most sum min(d,k); each pooled group also sends d public bits plus framing. Select a group only after accounting for actual ciphertext widths, work, and the number of decryptions on a selected branch. For example a branch using one occurrence may be cheaper to decrypt directly even when pooling saves Enc work.

For a false type first replace its encrypted seed bits by encryptions of zero, then replace the expansion by an independent uniform string. The seed is absent from the remaining transcript, and the uniform mask hides the whole vector jointly. After switching all false types, revealing all payloads for true types is safe on an unauthorized set by the AND/OR sharing argument. In an ideal unauthorized view the distribution of these revealed payloads is identical for both messages. Charge both message experiments, at most k bit-WE hops and one generator hop per pooled false type per experiment, and the ordinary false-leaf hops for unpooled types. A quantum-secure classical-output PRG is needed only for this option. The SHAKE listing tests layout and correctness only. If computing d output bits or emitting the expanded layout exceeds the global polynomial cap, take the fallback.

### Bounds and experiments

Bound the number of states and explicit edges before allocation, the total canonical syntax size, antichain insertions/comparisons, dualization, factoring and output size. The core operations are polynomial per budget unit using explicit finite bitsets, DAGs and formula trees. A prefix or terminal antichain may be exponential. Abandoning the reachability computation requires a sound fallback; a truncated antichain could lose real witnesses. If the complete DNF already exists, an aborted optional dual or factor search can keep that DNF if it fits. In the listings, the edge layout is supplied already bounded. The Python recursion depth also bounds the factor prototype; a bounded dispatcher must handle exhaustion or use an explicit stack. Charge the witness trace, maps, and ciphertext scan to Dec. Together with a polynomial-time, polynomial-ciphertext leaf backend and fallback, all three worst-case costs remain polynomial jointly in security and input length. The registered quantum-safe construction for arbitrary hard leaves remains unresolved.

* On 120 small randomized raw circuits the test compared all 2898 original traces to the compiled interface, including 3406 individual decryptions on valid witnesses across both bits. It independently checked 3277 local endpoint/witness evaluations and 7680 truth assignments for abstract labeled graphs against directed reachability, the dual CNF, and the emitted formula.
* For three 128-input, 4096-gate controls a common mode bit chooses a local guard in each of 32 bags, with independent private inputs. All have 488 candidate transitions. One gives two nonconstant types and a one-leaf access formula. Varying the guards gives four types and a three-leaf formula. Making both options in the last bag contradictory gives constant false with zero encrypted leaves. The planted witnesses and small predicates make these checks illustrative. A public SAT shortcut can win.
* An eight-bag, 4096-gate conjunction with strictly increasing local guard prefixes gives 15 nonconstant types. Equality-only compilation encrypts eight leaves. Twenty-eight proper conjunct projections reduce this to one, the strongest guard, and 896 sampled source-to-target witness implications were checked. No PRG is used.
* A separate family uses four fresh sets of 31 private inputs with the same 120-clause CNF template and a carried conjunction. The compiler produces one opaque 31-input predicate without tabulating its 2^31 witnesses. The same signed-AND simplifier and first-use variable ordering are applied to the full circuit and the leaf. Feed both into the live-clause matrix compiler of [PR 99](https://github.com/MachinaIO/SigabaPark/pull/99). At a fixed scale m=alpha*w the interior residue count is 2(h-2)w² alpha². On the three planted seeds 81–83 the full-to-leaf interior ratio is 4.057–4.058. On unplanted seed 901 the shapes are (1551,456) and (387,454), and the coefficients are 644185728 and 158709320, ratio 4.059. The success or failure of the unplanted CNF is not needed or asserted. This control directly exploits repetition of independently witnessed subproblems. It measures compiled matrix dimensions, not a lattice security level, total bytes or measured encryption time.
* Distinct incomparable types may give no compression. The unconditional algebraic transformations preserve whichever leaf assumptions the backend needed. The conditional polynomial benchmark of PR 99 still uses additional assumptions beyond ordinary registered LWE.

The shortened matrix backend also permits an end-to-end count for the encrypted part. Including both endpoints, h>=2 levels and m columns give C=2m(1+t)+2(h-2)m² transmitted residues, P=2((h-2)m+t) sampled preimage columns, and D=(h-2)m²+mt selected modular multiply-adds in Dec. For each of the four measured templates the listing verifies coefficient inequalities implying C_full>4 C_leaf, P_full>4 P_leaf and D_full>4 D_leaf for *every* common integral alpha>=1 and 1<=t<=alpha*w_leaf. The full scheme also has over four times as many levels. For unplanted seed 901 these three strict inequalities are the second Lean theorem, with the measured shapes supplied as inputs. This comparison uses fresh matrices and the same modulus and scale on both sides, with framing omitted; the single-leaf tree requires no public masks. It covers the complete matrix payload and these two operation counts, without claiming measured runtime, a security parameter selection, or a fourfold reduction in total machine steps including compilation and witness conversion.

To reproduce, take nand.py from the second listing in [PR 102 at d49bd9e](https://github.com/MachinaIO/SigabaPark/blob/d49bd9eeb7d5a4cacdfd6b4d774348e55ad6a0f9/dag/Notes/pq-we-separator-paths.md) and frontend.py from the first listing in [PR 99 at 58036ab](https://github.com/MachinaIO/SigabaPark/blob/58036abbee86216e6e0bf18a4a8234c6d55d82cb/dag/Notes/pq-we-live-clause-matrix-product.md). Run the four listings as python labels.py nand.py, python implications.py labels.py nand.py, python shapes.py labels.py nand.py frontend.py, and python pads.py.

~~~python
"""Bounded compiler for repeated local predicates. Syntax and witness maps are public."""
from itertools import product
from random import Random
from functools import lru_cache
from collections import Counter

class Budget(Exception):pass

def canonical(plan,n,i,a,b):
    gates,cuts,bd,priv=plan
    # Literal 1 is true, -1 false. Positive node IDs start at 2.
    d={0:1};nodes={};ops={};inp={}
    for j,x in enumerate(priv[i]):
        idx=2+len(nodes);nodes[idx]=('x',j);inp[idx]=j;d[x]=idx
    def conj(u,v):
        if u==-1 or v==-1 or u==-v:return -1
        if u==1 or u==v:return v
        if v==1:return u
        k=('and',*sorted((u,v)))
        if k not in ops:
            j=2+len(nodes);nodes[j]=k;ops[k]=j
        return ops[k]
    for j,x in enumerate(bd[i]):d[x]=1 if a>>j&1 else -1
    desired={x:(1 if b>>j&1 else -1) for j,x in enumerate(bd[i+1])}
    if any(x in d and d[x]!=v for x,v in desired.items()):return ((),-1),()
    for x,v in desired.items():
        if x<=n:d[x]=v
    for j in range(cuts[i],cuts[i+1]):
        u,v=gates[j];d[n+j+1]=-conj(d[u],d[v])
    out=1
    for x,v in desired.items():out=conj(out,v*d[x])
    if i==len(priv)-1:out=conj(out,d[n+len(gates)] if gates else 1)
    # Keep only reachable nodes, then rename the private inputs and operations.
    used={abs(out)}
    for idx in reversed(nodes):
        if idx in used and nodes[idx][0]=='and':used.update(abs(t) for t in nodes[idx][1:])
    remap={1:1};key=[];ports=[]
    def lit(x):return (1 if x>0 else -1)*remap[abs(x)]
    for idx,op in nodes.items():
        if idx not in used:continue
        remap[idx]=2+len(key)
        if idx in inp:
            key.append(('x',len(ports)));ports.append(inp[idx])
        else:key.append(('and',*sorted(lit(x) for x in op[1:])))
    return (tuple(key),lit(out)),tuple(ports)

def checkkey(key,word):
    nodes,out=key;d=[0,1]
    def val(x):return d[abs(x)]^(x<0)
    for op in nodes:d.append(word>>op[1]&1 if op[0]=='x' else val(op[1])&val(op[2]))
    return val(out)

class Limit:
    def __init__(self,n):self.left=n
    def tick(self,n=1):
        self.left-=n
        if self.left<0:raise Budget

def insert(xs,a,limit):
    limit.tick(1+2*len(xs))
    if any(x&a==x for x in xs):return
    xs[:]=[x for x in xs if x&a!=a]
    xs.append(a)

def path_terms(sizes,label,limit):
    cur=[[0]]
    for i,(l,r) in enumerate(zip(sizes,sizes[1:])):
        nxt=[[] for _ in range(r)]
        for a in range(l):
            for b in range(r):
                z=label[i,a,b];limit.tick()
                if z is not None:
                    for mask in cur[a]:insert(nxt[b],mask|z,limit)
        cur=nxt
    return tuple(sorted(cur[0]))

def blockers(terms,limit):
    cur=[0]
    for term in terms:
        nxt=[]
        for c in cur:
            if c&term:insert(nxt,c,limit);continue
            rem=term
            while rem:
                bit=rem&-rem;rem-=bit;insert(nxt,c|bit,limit)
        cur=nxt
    return tuple(sorted(cur))

def circuit(terms,limit):
    # Return an AND/OR tree. Absorbing constants are free. Only invoked with budget.
    T=('const',1);F=('const',0)
    def combine(op,items):
        neutral=T if op=='and' else F;absorbing=F if op=='and' else T
        out=[]
        for x in items:
            if x==absorbing:return absorbing
            if x!=neutral:out.append(x)
        if not out:return neutral
        if len(out)==1:return out[0]
        return (op,*out)
    def flat(family,dual):
        op='or' if dual else 'and';outer='and' if dual else 'or'
        return combine(outer,[combine(op,[('var',i) for i in range(t.bit_length()) if t>>i&1]) for t in family])
    def size(tree):return 1 if tree[0]=='var' else 0 if tree[0]=='const' else sum(map(size,tree[1:]))
    best=flat(terms,False)
    try:
        dual=flat(blockers(terms,limit),True)
        if size(dual)<size(best):best=dual
    except Budget:return best
    @lru_cache(None)
    def factor(ts):
        limit.tick(1+len(ts))
        if not ts:return F
        if ts[0]==0:return T
        out=flat(ts,False);cost=size(out);bits=0
        for t in ts:bits|=t
        while bits:
            bit=bits&-bits;bits-=bit;var=('var',bit.bit_length()-1)
            off=tuple(t for t in ts if not t&bit);on=[]
            for t in ts:insert(on,t&~bit,limit)
            f0=factor(off);f1=factor(tuple(sorted(on)))
            for cand in (combine('or',[f0,combine('and',[var,f1])]),
                         combine('and',[f1,combine('or',[var,f0])])):
                score=size(cand)
                if score<cost:out,cost=cand,score
        return out
    try:
        cand=factor(terms)
        if size(cand)<size(best):best=cand
    except Budget:pass
    return best

def evaluate(tree,vals):
    op=tree[0]
    if op=='const':return bool(tree[1])
    if op=='var':return bool(vals>>tree[1]&1)
    return (all if op=='and' else any)(evaluate(t,vals) for t in tree[1:])

def frontend(plan,n):
    d=tuple(1<<len(x) for x in plan[2]);keys={};edges={};maps={}
    for i,(l,r) in enumerate(zip(d,d[1:])):
        for a,b in product(range(l),range(r)):
            k,ports=canonical(plan,n,i,a,b);z=k[1]
            code=0 if z==1 else None if z==-1 else 1<<keys.setdefault(k,len(keys))
            edges[i,a,b]=code;maps[i,a,b]=(k,ports)
    return d,edges,keys,maps

def formula_enc(tree,bit,keys,rng):
    if tree[0]=='const':return ('public',bit if tree[1] else 0)
    if tree[0]=='var':
        k=keys[tree[1]]
        # Small exact decision WE for verification only.
        m=sum(op[0]=='x' for op in k[0])
        return ('leaf',bit if any(checkkey(k,w) for w in range(1<<m)) else 0)
    msgs=[bit]*(len(tree)-1)
    if tree[0]=='and':
        for j in range(len(msgs)-1):msgs[j]=rng.randrange(2);msgs[-1]^=msgs[j]
    return (tree[0],*(formula_enc(t,m,keys,rng) for t,m in zip(tree[1:],msgs)))

def formula_dec(tree,ct,certs):
    if tree[0]=='const':return ct[1] if tree[1] else None
    if tree[0]=='var':return ct[1] if tree[1] in certs else None
    acc=0
    for t,c in zip(tree[1:],ct[1:]):
        v=formula_dec(t,c,certs)
        if tree[0]=='or':
            if v is not None:return v
        elif v is None:return None
        else:acc^=v
    return acc if tree[0]=='and' else None

def size(t):return 1 if t[0]=='var' else 0 if t[0]=='const' else sum(map(size,t[1:]))

def trace(n,gates,word):
    d=[1]+[word>>i&1 for i in range(n)]
    for u,v in gates:d.append(1-d[u]*d[v])
    return d

def experiment(n,gates,cuts,schedule,words,report=False):
    p=schedule(n,gates,cuts);dims,edges,ids,maps=frontend(p,n)
    terms=path_terms(dims,edges,Limit(300000));tree=circuit(terms,Limit(200000))
    keys=list(ids);rng=Random(18);ct=[formula_enc(tree,b,keys,rng) for b in (0,1)]
    feasible=sum(1<<i for i,k in enumerate(keys) if any(checkkey(k,w) for w in range(1<<sum(op[0]=='x' for op in k[0]))))
    has=False;used=0
    for word in words:
        d=trace(n,p[0],word);has|=bool(d[-1])
        if not d[-1]:continue
        pack=lambda vs:sum(d[x]<<j for j,x in enumerate(vs))
        certs={}
        for i in range(len(cuts)-1):
            e=(i,pack(p[2][i]),pack(p[2][i+1]))
            k,ports=maps[e];local=pack(p[3][i]);canonicalword=sum((local>>j&1)<<b for b,j in enumerate(ports))
            assert checkkey(k,canonicalword)
            if k in ids:certs[ids[k]]=canonicalword
        assert evaluate(tree,sum(1<<j for j in certs))
        for b in (0,1):assert formula_dec(tree,ct[b],certs)==b
        used+=1
    if n<=7:assert evaluate(tree,feasible)==has
    if report:print('bags, physical edges, types, minterms, encrypted leaf bits, passing sample traces',len(cuts)-1,len(edges),len(keys),len(terms),size(tree),used)
    return size(tree),used

def tests(schedule):
    rng=Random(826);cases=0;yes=0
    for _ in range(120):
        n=rng.randint(1,6);gates=[tuple(rng.randrange(n+j+3) for _ in range(2)) for j in range(6)]
        _,cnt=experiment(n,gates,[0,2,4,6],schedule,range(1<<n));yes+=cnt;cases+=1<<n
    print('original traces, successful paired-bit decryptions:',cases,2*yes)
    edges_checked=0
    for _ in range(60):
        n=4;g=[tuple(rng.randrange(n+j+3) for _ in range(2)) for j in range(6)]
        p=schedule(n,g,[0,2,4,6]);_,_,_,maps=frontend(p,n)
        for (i,a,b),(k,ports) in maps.items():
            for local in range(1<<len(p[3][i])):
                w=sum((local>>j&1)<<b for b,j in enumerate(ports))
                norm,cuts,bd,priv=p
                d={0:1,**{x:a>>j&1 for j,x in enumerate(bd[i])}}
                want={x:b>>j&1 for j,x in enumerate(bd[i+1])}
                valid=all(d[x]==v for x,v in want.items() if x in d)
                d.update({x:v for x,v in want.items() if x<=n})
                d.update({x:local>>j&1 for j,x in enumerate(priv[i])})
                for j in range(cuts[i],cuts[i+1]):
                    u,v=norm[j];d[n+j+1]=1-d[u]*d[v]
                valid=valid and all(d[x]==v for x,v in want.items()) and (i<len(priv)-1 or d[n+len(g)])
                assert bool(checkkey(k,w))==bool(valid)
                edges_checked+=1
    print('local endpoint/witness evaluations:',edges_checked)
    # Compare graph reachability and both monotone normal forms for every type subset.
    count=0
    for _ in range(120):
        d=(1,2,3,2,1);L=6
        labels={(i,a,b):rng.choice([None,0]+[1<<j for j in range(L)]) for i in range(4) for a in range(d[i]) for b in range(d[i+1])}
        terms=path_terms(d,labels,Limit(200000));cuts=blockers(terms,Limit(200000));tree=circuit(terms,Limit(200000))
        for m in range(1<<L):
            st={0}
            for i in range(4):
                st={b for a in st for b in range(d[i+1]) if labels[i,a,b] is not None and labels[i,a,b]&m==labels[i,a,b]}
            assert (0 in st)==evaluate(tree,m)==any(t&m==t for t in terms)==all(c&m for c in cuts)
            count+=1
    print('abstract type truth vectors:',count)
    for variant in (0,1,2):
        # Mode bit chooses one of two local tests. Fresh private bits per bag.
        n=128;g=[];last=0
        def nand(a,b):
            g.append((a,b));return n+len(g)
        def and_(a,b):
            v=nand(a,b);return nand(v,v)
        def mux(m,a,b):return nand(nand(m,a),nand(nand(m,m),b))
        for i in range(32):
            a,b,c=2+3*i,3+3*i,4+3*i
            left=nand(a,b) if variant==0 or i%2==0 else and_(a,nand(b,c))
            right=and_(b,c) if i%3 else nand(c,a)
            if variant==2 and i==31:right=and_(right,nand(right,right));left=and_(left,nand(left,left))
            guard=mux(1,left,right)
            last=and_(last,guard)
            gap=(i+1)*128-len(g)
            if gap%2:nand(0,0)
            for _ in range(gap//2):v=nand(last,last);last=nand(v,v)
        words=[0,1,(1<<128)-1,1+sum(1<<(1+3*i) for i in range(32)),sum(6<<(1+3*i) for i in range(32))]+[rng.getrandbits(128) for _ in range(25)]
        experiment(n,g,list(range(0,4097,128)),schedule,words,True)
if __name__=='__main__':
    import runpy,sys
    tests(runpy.run_path(sys.argv[1])['schedule'])
~~~

~~~python
"""Witness-preserving implications from positive conjuncts of canonical AND DAGs."""
from itertools import product
from random import Random
import sys,runpy

def subtree(key,out):
    ops,_=key;live={abs(out)}
    for idx in range(len(ops)+1,1,-1):
        op=ops[idx-2]
        if idx in live and op[0]=='and':live.update(abs(x) for x in op[1:])
    names={1:1};new=[];ports=[]
    def lit(x):return names[abs(x)]*(1 if x>0 else -1)
    for i,op in enumerate(ops,2):
        if i not in live:continue
        names[i]=2+len(new)
        if op[0]=='x':
            new.append(('x',len(ports)));ports.append(op[1])
        else:new.append(('and',*sorted(lit(x) for x in op[1:])))
    return (tuple(new),lit(out)),tuple(ports)

def implications(keys,limit):
    ids={k:j for j,k in enumerate(keys)};maps={}
    for i,key in enumerate(keys):
        ops,out=key;todo=[out];seen=set()
        while todo:
            v=todo.pop()
            if v in seen:continue
            seen.add(v);limit.tick(1+len(ops))
            sub,ports=subtree(key,v)
            if sub in ids and ids[sub]!=i:maps[i,ids[sub]]=ports
            if v>1 and ops[v-2][0]=='and':todo.extend(ops[v-2][1:])
    closure=[1<<i for i in range(len(keys))]
    for i,j in maps:closure[i]|=1<<j
    # Every edge decreases key size, so one increasing-size pass suffices.
    for i in sorted(range(len(keys)),key=lambda j:len(keys[j][0])):
        for a,b in maps:
            if a==i:closure[a]|=closure[b]
    return maps,closure

def compile_closed(d,edges,closure,lib,limit):
    lifted={e:(v if not v else closure[v.bit_length()-1]) for e,v in edges.items()}
    terms=lib['path_terms'](d,lifted,limit)
    reduced=[]
    for t in terms:
        keep=t
        for i,row in enumerate(closure):
            if t>>i&1:keep &= ~(row&~(1<<i))
        lib['insert'](reduced,keep,limit)
    return lib['circuit'](tuple(sorted(reduced)),limit)

def extend(certs,maps,keys):
    certs=dict(certs)
    for i in sorted(range(len(keys)),key=lambda j:len(keys[j][0]),reverse=True):
        if i in certs:
            for (a,b),ports in maps.items():
                if a==i and b not in certs:
                    certs[b]=sum((certs[i]>>j&1)<<z for z,j in enumerate(ports))
    return certs

def prefix_control(lib,base):
    n=128;g=[];prev=0;num=8
    def nand(x,y):g.append((x,y));return n+len(g)
    def both(x,y):v=nand(x,y);return nand(v,v)
    for i in range(num):
        vs=list(range(16*i+1,16*i+17));guard=0
        for j in range(i+1):guard=both(guard,nand(vs[j],vs[15-j]))
        prev=both(prev,guard)
        gap=(i+1)*512-len(g)
        if gap%2:nand(0,0)
        for _ in range(gap//2):v=nand(prev,prev);prev=nand(v,v)
    p=base['schedule'](n,g,list(range(0,4097,512)));d,edges,ids,em=lib['frontend'](p,n)
    keys=list(ids);limit=lib['Limit'](10**7)
    plain=lib['circuit'](lib['path_terms'](d,edges,limit),limit)
    maps,cl=implications(keys,limit);compact=compile_closed(d,edges,cl,lib,limit)
    rng=Random(617);cnt=0
    for word in [0]+[rng.getrandbits(128) for _ in range(50)]:
        tr=lib['trace'](n,p[0],word)
        if not tr[-1]:continue
        pack=lambda vs:sum(tr[x]<<j for j,x in enumerate(vs));cert={}
        for i in range(num):
            k,ports=em[i,pack(p[2][i]),pack(p[2][i+1])]
            w=pack(p[3][i]);w=sum((w>>j&1)<<b for b,j in enumerate(ports))
            if k in ids:cert[ids[k]]=w
        cert=extend(cert,maps,keys)
        assert all(lib['checkkey'](keys[j],w) for j,w in cert.items())
        assert lib['evaluate'](compact,sum(1<<j for j in cert));cnt+=1
    tested=0
    for (a,b),ports in maps.items():
        nbits=sum(op[0]=='x' for op in keys[a][0])
        for w in [0,(1<<nbits)-1]+[rng.getrandbits(nbits) for _ in range(30)]:
            weak=sum((w>>j&1)<<i for i,j in enumerate(ports))
            assert not lib['checkkey'](keys[a],w) or lib['checkkey'](keys[b],weak)
            tested+=1
    print('prefix guards: types, strict transports, equality-only calls, implication-aware calls, mapped inputs checked',len(keys),len(maps),lib['size'](plain),lib['size'](compact),tested)
    assert cnt and lib['size'](compact)<=lib['size'](plain)
if __name__=='__main__':prefix_control(*(runpy.run_path(p) for p in sys.argv[1:]))
~~~

~~~python
"""Large-private-input control. The compiler never enumerates the 31-bit domain."""
import sys,runpy
from random import Random

def control(seed):
    n=128;g=[];prior=0;bags=4;plant=(1<<31)-1
    rng=Random(seed)
    template=[]
    for _ in range(120):
        vs=rng.sample(range(31),3);sign=[rng.choice((1,-1)) for _ in vs]
        if seed<900 and max(sign)<0:sign[0]=1
        template.append(tuple((v+1)*s for v,s in zip(vs,sign)))
    def nand(a,b):
        g.append((a,b));return n+len(g)
    for group in range(bags):
        pos=[1+31*group+j for j in range(31)]
        neg=[nand(x,x) for x in pos];cur=0
        for row in template:
            # OR all three literals, then conjoin with the running bit.
            a,b,c=[(neg if k>0 else pos)[abs(k)-1] for k in row]
            o=nand(a,b);cl=nand(nand(o,o),c);u=nand(cl,cur);cur=nand(u,u)
        s=nand(prior,cur);prior=nand(s,s)
        gap=(group+1)*1024-len(g);assert gap>=0
        if gap%2:nand(0,0)
        for _ in range(gap//2):q=nand(prior,prior);prior=nand(q,q)
    return n,g,list(range(0,4097,1024)),sum(plant<<(31*i) for i in range(4))

def matrix_shape(key,compiler):
    ops,out=key
    if abs(out)==1:return (0,0)
    # Rename in first-use order so future private inputs need not all be read first.
    names={};rows=[]
    def lit(t):
        a=names.setdefault(abs(t),len(names)+1)
        return a if t>0 else -a
    for x,op in enumerate(ops,2):
        if op[0]=='and':
            a,b,z=lit(op[1]),lit(op[2]),lit(x)
            rows.extend([(-z,a),(-z,b),(z,-a,-b)])
    rows.append((lit(out),))
    pr=compiler(rows,len(names),0)
    return len(pr[1]),len(pr[0])
def run(lib,base,front):
    for seed in (81,82,83,901):
        n,g,cuts,word=control(seed);p=base['schedule'](n,g,cuts)
        d,edges,ks,maps=lib['frontend'](p,n)
        t=lib['circuit'](lib['path_terms'](d,edges,lib['Limit'](100000)),lib['Limit'](100000))
        assert t[0]=='var'
        k=list(ks)[t[1]]
        mon=base['schedule'](n,g,[0,len(g)])
        k0,_=lib['canonical'](mon,n,0,0,0)
        # Replay the planted original witness through the actual canonical witness map.
        trace=lib['trace'](n,p[0],word)
        if seed<900:assert trace[-1]
        pack=lambda vs:sum(trace[x]<<j for j,x in enumerate(vs))
        used=False
        for i in range(len(cuts)-1):
            key,ports=maps[i,pack(p[2][i]),pack(p[2][i+1])]
            local=pack(p[3][i]);w=sum((local>>j&1)<<b for b,j in enumerate(ports))
            if trace[-1]:assert lib['checkkey'](key,w)
            used|=key==k
        if trace[-1]:assert used
        m,l=[matrix_shape(key,front['compile_program']) for key in (k0,k)]
        coeff=lambda h:2*(h[0]-2)*h[1]**2
        # For every common alpha>=1 and 1<=t<=alpha*local_width:
        # lower-bound full-minus-four-local costs by using t<=alpha*local_width.
        H,W=m;h,w=l
        inner=(H-2)*W**2-4*(h-2)*w**2
        border=4*w-W
        assert border>=0 and inner>border*(w+1) # two endpoints incl. root
        assert (H-2)*W-4*(h-2)*w>3*w # preimage columns incl. final t
        assert H>4*h
        print('coefficients certifying >4x for payload, MACs, sampled columns:',
              inner,border,(H-2)*W-4*(h-2)*w)
        print('seed / full and leaf (levels,width) / interior coefficients / quotient:',
              seed,m,l,coeff(m),coeff(l),round(coeff(m)/coeff(l),3))
if __name__=='__main__':run(*(runpy.run_path(x) for x in sys.argv[1:]))
~~~

~~~python
from hashlib import shake_256
from random import Random

def padbits(seed,n,k):
    data=seed.to_bytes((k+7)//8,'big')
    return int.from_bytes(shake_256(data).digest((n+7)//8),'little')% (1<<n)
def group(bits,k,leaf_encrypt,rng):
    n=len(bits);raw=sum(b<<j for j,b in enumerate(bits))
    if n<=k:return ('direct',n,[leaf_encrypt(b) for b in bits],0)
    seed=rng.randrange(1<<k)
    return ('seed',n,[leaf_encrypt(seed>>j&1) for j in range(k)],raw^padbits(seed,n,k))
def read(ct,leaf_decrypt,k):
    kind,n,blocks,mask=ct
    val=sum(leaf_decrypt(c)<<j for j,c in enumerate(blocks))
    return val if kind=='direct' else mask^padbits(val,n,k)
def test():
    rng=Random(1001);groups=0
    for k in (8,16,128):
        for n in (1,k-1,k,k+1,4*k+3):
            bs=[rng.randrange(2) for _ in range(n)]
            # A toy, directly decidable YES leaf with witness 7.
            ct=group(bs,k,lambda b:b,rng)
            assert len(ct[2])==min(k,n)
            assert read(ct,lambda c:c,k)==sum(v<<j for j,v in enumerate(bs))
            groups+=1
    print('round-trip direct/seed groups:',groups)
if __name__=='__main__':test()
~~~

The fifth listing is a bounded public dispatcher for the information-theoretic compiler, with explicit leaf Enc and Dec callbacks. Run python dispatch.py labels.py implications.py nand.py. It constructs the whole-circuit canonical leaf first, checks separator and candidate-edge budgets before enumerating states, keeps a completed equality-only plan if the implication search exhausts its budget, and accepts a smaller plan using the supplied positive polynomial-time cost estimate. The default weight is program length plus one. Both parties can deterministically recompute the layout from the public input and configuration. Decryption projects the supplied original witness, verifies canonical certificates and selects authorized OR children before invoking leaf decryption. The optional seed wrapper is not needed by this entry point. Across 100 circuits and three caps it selected the whole leaf 206 times, a split tree 61 times, and a constant 33 times. All 11202 decryptions using valid witnesses returned the requested bits with the small exact-decision leaf. A separate exhaustive coin enumeration verified 362 complete unauthorized transcript histograms on AND/OR formulas with repeated predicates. This exercises the fallback and message handling under the stated backend interface.

~~~python
"""Bounded public compiler and callback-based Enc/Dec of the chosen representation."""
from random import Random
import sys,runpy

def choose(lib,imp,schedule,n,gates,cuts,requested,weight=None):
    weight=weight or (lambda key:1+len(key[0]))
    # The single bag without gates is the constant true predicate.
    if not gates:return dict(mode='constant',tree=('const',1),keys=[])
    one=schedule(n,gates,[0,len(gates)])
    mon,ports=lib['canonical'](one,n,0,0,0)
    if abs(mon[1])==1:return dict(mode='constant',tree=('const',int(mon[1]>0)),keys=[])
    fallback=dict(mode='whole',tree=('var',0),keys=[mon],ports=ports,private=one[3][0])
    cap=min(requested,64*(1+n+len(gates))**2)
    if cap<=0:return fallback
    plan=schedule(n,gates,cuts);bd=plan[2]
    if any(len(x)>=cap.bit_length() for x in bd):return fallback
    dims=[1<<len(x) for x in bd]
    if sum(a*b for a,b in zip(dims,dims[1:]))>cap:return fallback
    dims,edges,ids,maps=lib['frontend'](plan,n);keys=list(ids)
    def cost(tree):
        op=tree[0]
        if op=='const':return 0
        if op=='var':return weight(keys[tree[1]])
        return sum(cost(t) for t in tree[1:])
    found=fallback;smallest=weight(mon)
    def consider(tree,translations):
        nonlocal found,smallest
        stack=[(tree,0)]
        while stack:
            node,depth=stack.pop()
            if depth>120:return
            if node[0] in ('and','or'):stack.extend((ch,depth+1) for ch in node[1:])
        count=lib['size'](tree)
        if count>cap:return
        c=cost(tree)
        if c<smallest:
            found=dict(mode='split',tree=tree,keys=keys,plan=plan,maps=maps,
                       ids=ids,translations=translations)
            smallest=c
    # Each attempt has its own cap, so a failed optional phase preserves a completed plan.
    try:
        limit=lib['Limit'](cap)
        terms=lib['path_terms'](dims,edges,limit)
        consider(lib['circuit'](terms,limit),{})
    except (lib['Budget'],RecursionError):pass
    try:
        limit=lib['Limit'](cap)
        tr,cl=imp['implications'](keys,limit)
        if tr:consider(imp['compile_closed'](dims,edges,cl,lib,limit),tr)
    except (lib['Budget'],RecursionError):pass
    return found

def encrypt(comp,bit,coin,enc_leaf):
    keys=comp['keys']
    def emit(t,m):
        op=t[0]
        if op=='const':return m if t[1] else 0
        if op=='var':return enc_leaf(keys[t[1]],m)
        shares=[m]*(len(t)-1)
        if op=='and':
            for j in range(len(shares)-1):
                shares[j]=coin();shares[-1]^=shares[j]
        return [emit(c,b) for c,b in zip(t[1:],shares)]
    return emit(comp['tree'],bit)

def decrypt(lib,imp,comp,ct,n,word,dec_leaf):
    certs={};keys=comp['keys']
    def pack(x,ports):return sum((x>>j&1)<<i for i,j in enumerate(ports))
    if comp['mode']=='whole':
        local=pack(word,[x-1 for x in comp['private']])
        w=pack(local,comp['ports'])
        if lib['checkkey'](keys[0],w):certs[0]=w
    elif comp['mode']=='split':
        plan=comp['plan'];tr=lib['trace'](n,plan[0],word)
        wirebits=lambda xs:sum(tr[x]<<j for j,x in enumerate(xs))
        for i,vs in enumerate(plan[3]):
            e=(i,wirebits(plan[2][i]),wirebits(plan[2][i+1]))
            k,ports=comp['maps'][e]
            if k in comp['ids']:
                w=pack(wirebits(vs),ports)
                if lib['checkkey'](k,w):certs[comp['ids'][k]]=w
        certs=imp['extend'](certs,comp['translations'],keys)
    present=sum(1<<i for i in certs)
    def open_node(t,c):
        op=t[0]
        if op=='const':return c if t[1] else None
        if op=='var':return dec_leaf(keys[t[1]],c,certs[t[1]])
        if op=='or':
            for j,child in enumerate(t[1:]):
                if lib['evaluate'](child,present):return open_node(child,c[j])
            return None
        b=0
        for j,child in enumerate(t[1:]):
            value=open_node(child,c[j])
            if value is None:return None
            b^=value
        return b
    if not lib['evaluate'](comp['tree'],present):return None
    return open_node(comp['tree'],ct)

def test(lib,imp,base):
    rng=Random(1337);counts={};opens=0
    for case in range(100):
        n=5;g=[tuple(rng.randrange(n+j+3) for _ in range(2)) for j in range(8)]
        norm=base['schedule'](n,g,[0,8])[0]
        for cap in (0,20,10000):
            comp=choose(lib,imp,base['schedule'],n,g,[0,2,4,6,8],cap)
            counts[comp['mode']]=1+counts.get(comp['mode'],0)
            def enc(k,b):
                d=sum(op[0]=='x' for op in k[0])
                return b if any(lib['checkkey'](k,w) for w in range(1<<d)) else 0
            def dec(k,c,w):
                assert lib['checkkey'](k,w);return c
            for b in (0,1):
                ct=encrypt(comp,b,lambda:rng.randrange(2),enc)
                for word in range(1<<n):
                    if lib['trace'](n,norm,word)[-1]:
                        assert decrypt(lib,imp,comp,ct,n,word,dec)==b;opens+=1
    assert 'split' in counts and 'whole' in counts
    print('dispatcher mode frequencies, valid decryptions:',counts,opens)
    # Equality of the complete ideal-leaf transcript for every unauthorized set.
    from itertools import product
    from collections import Counter
    def norm(c):return tuple(map(norm,c)) if isinstance(c,list) else c
    tests=0
    for _ in range(45):
        def build(depth):
            if depth==0 or rng.randrange(4)==0:return ('var',rng.randrange(4))
            return (rng.choice(('and','or')),build(depth-1),build(depth-1))
        tree=build(3);comp=dict(keys=list(range(4)),tree=tree)
        def num(t):
            if t[0]=='var':return 0
            return (len(t)-2 if t[0]=='and' else 0)+sum(num(v) for v in t[1:])
        for live in range(16):
            if lib['evaluate'](tree,live):continue
            bins=[Counter(),Counter()]
            for b in (0,1):
                for bits in product(range(2),repeat=num(tree)):
                    it=iter(bits)
                    ct=encrypt(comp,b,lambda:next(it),lambda i,m:m if live>>i&1 else 0)
                    bins[b][norm(ct)]+=1
            assert bins[0]==bins[1];tests+=1
    print('exact unauthorized transcript histograms',tests)
if __name__=='__main__':test(*(runpy.run_path(p) for p in sys.argv[1:]))
~~~
