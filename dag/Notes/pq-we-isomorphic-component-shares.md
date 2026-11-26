---
title: Encrypt repeated separator components once using signed witness maps
refs: [definition:WE_CircuitSAT, note:pq-we-projected-component-encoder]
tags: [witness-encryption, compilation, correctness, complexity]
---

In the separator encoder each branch encrypts the same bit and each component of a conjunction receives an independent XOR share (subject to parity). Two components may differ syntactically while asking precisely the same SAT question under variable renaming and complementation. The following compiler factors the public relation *before drawing shares*. Independent copies of ciphertexts carrying different shares cannot simply be removed after encryption.

**Exact certificates under a public search cap.** For each component try signed bijections from its variables onto consecutive canonical variables. For each sign compute the sorted multiset of lengths of incident clauses. The unordered pair of signatures is a variable color. Order by that color, enumerate tied orders and ambiguous polarities up to a public cap, and retain the lexicographically smallest normalized clause tuple examined. Each retained tuple has an explicit signed witness map. Equal tuples give an exact isomorphism even if the search is capped. Different tuples can miss an isomorphism. The bounded iterative search uses at most the prescribed number of complete labelings and polynomial work per labeling. This is a restricted compiler for signed variable permutations, with no general SAT equivalence oracle.

**Factored relation.** In each separator branch, keep one representative of every distinct canonical component. All original components in a branch occupy disjoint variables, so a witness for one canonical representative can be mapped back independently to every copy. Across the live branches let C be the intersection of these sets and R_b the remaining components in branch b. The SAT condition is the conjunction of all components in C and the disjunction of the two residual conjunctions. A branch containing an empty clause is false and may be ignored. If any live residual is an empty conjunction, the residual disjunction is true and can be omitted. Constants have the usual public YES/NO encoding. The reverse direction chooses one live branch, transports canonical models back to its disjoint components, sets the separator and then lifts the prior eliminated variables. This proves no spurious accepting witness exists.

**Enc and Dec.** Split the message into XOR shares for the common components and, when needed, one additional share for the residual disjunction. Encrypt the latter share in both live branches, splitting again inside each residual conjunction. Dec takes the actual separator bit from the original valid witness. For each common ciphertext it uses the signed map for *that branch*, which need not refer to the same original variables or polarities in the other branch. The chosen residual similarly uses its own maps. The resulting valid canonical witnesses decrypt the requisite shares; XOR recovers the bit. False-instance hiding and valid-witness error compose by the same OR hybrids and AND sharing argument as in the preceding note, including its adversary-model caveat for choosing a false child. The outer factoring requires no additional computational assumption. Metadata and map selection depend only on the statement; charge preprocessing and metadata if they are not public inputs to Dec.

**Accounts.** On the earlier 102- and 130-clause controls no common component was found across the two branches. Any observed savings there came from the changed variable order of canonicalized leaves. A separate connected 369-clause control uses four eight-variable modules under each branch, with signed permutations, a duplicate and branch-specific cores. With the same canonical variable order and the same per-leaf parameter calculator on both sides, the ordinary split costs 94280133776640 payload bits, 6458592 sampled columns and 372916975872 worst-path multiply-adds. Factoring reduces these to 47140066888320 bits, 3229296 columns and 283609895744 multiply-adds. Two canonical conditions are common; one residual condition remains per branch. The sample parameters measure honest resources and omit framing, runtime and security-matched dimensions. The module control is structured and no claim is made about its computational hardness. For public selection compare these three metrics with the existing monolithic/component baseline and keep a factored plan only when none increases.

**Verification.** On 64 small generated CNFs, the code exhaustively tested 680 valid assignment/message combinations using an ideal SAT leaf and verified the signed canonical witness at each actually decrypted leaf. For all 30 false instances, exhaustive enumeration of the XOR coins gave identical ideal ciphertext laws on the two message bits. The ideal leaf checks the combinatorics of the compiler, not a lattice security theorem.

~~~python
from collections import defaultdict

def canonical(C,cap=64):
    # A map lists the original signed literal for each positive canonical variable.
    if cap<1:
        raise ValueError("positive labeling budget required")
    variables=sorted({abs(x) for c in C for x in c})
    classes=defaultdict(list)
    signs={}
    for v in variables:
        pos=tuple(sorted(len(c) for c in C if v in c))
        neg=tuple(sorted(len(c) for c in C if -v in c))
        classes[tuple(sorted((pos,neg)))].append(v)
        signs[v]=(1,-1) if pos==neg else ((1,) if pos<neg else (-1,))
    # Iterative DFS, with a single iterator per label, avoids materializing factorial tables.
    ordered=[tuple(group) for _,group in sorted(classes.items()) for _ in group]
    def choices(i,used):
        return (sign*v for v in ordered[i] if v not in used for sign in signs[v])
    def maps():
        if not variables:
            yield ()
            return
        prefix=[];used=set();stack=[choices(0,used)]
        while stack:
            val=next(stack[-1],None)
            if val is None:
                stack.pop()
                if prefix:used.remove(abs(prefix.pop()))
            else:
                prefix.append(val);used.add(abs(val))
                if len(prefix)==len(variables):
                    yield tuple(prefix)
                    used.remove(abs(prefix.pop()))
                else:
                    stack.append(choices(len(prefix),used))
    best=None
    for i,order in enumerate(maps()):
        ids={abs(v):j if v>0 else -j for j,v in enumerate(order,1)}
        key=tuple(sorted(tuple(sorted(ids[abs(x)]*(1 if x>0 else -1) for x in c)) for c in C))
        if best is None or key<best[0]:best=(key,order)
        if i+1==cap:break
    return best

def layout(F,v,condition,components,cap=64):
    branches=[]
    for lit in (-v,v):
        G=condition(F,lit)
        if any(not c for c in G):
            branches.append(None)
            continue
        maps={}
        for C in components(G):
            key,order=canonical(C,cap)
            maps.setdefault(key,order)
        branches.append(maps)
    live=[b for b in branches if b is not None]
    common=sorted(set.intersection(*(set(b) for b in live))) if live else []
    rem=[None if b is None else sorted(set(b)-set(common)) for b in branches]
    return branches,common,rem

def share(value,N,randbit):
    shares=[randbit() for _ in range(N-1)]
    for s in shares:value^=s
    return shares+[value]

def encode(plan,bit,randbit,leaf):
    maps,common,rem=plan
    if all(b is None for b in maps):return ([],None)
    needs_or=all(t is None or len(t)>0 for t in rem)
    if not common and not needs_or:return ([],bit)
    ss=share(bit,len(common)+int(needs_or),randbit)
    ct=[leaf(key,s) for key,s in zip(common,ss)]
    tails=None
    if needs_or:
        tails=[None if r is None else [leaf(key,s) for key,s in zip(r,share(ss[-1],len(r),randbit))]
               for r in rem]
    return ct,tails

def decode(plan,ct,branch,x,leaf):
    maps,common,rem=plan
    if maps[branch] is None:return 0
    def read(key,c):
        wit=[int(bool(x[abs(lit)])==(lit>0)) for lit in maps[branch][key]]
        return leaf(key,c,wit)
    head,tails=ct
    if not common and isinstance(tails,int):return tails
    bit=0
    for key,c in zip(common,head):bit^=read(key,c)
    if tails is not None:
        for key,c in zip(rem[branch],tails[branch]):bit^=read(key,c)
    return bit

def select_plan(F,component,counts,bill,cap=64):
    residual,old=component['compile_tree'](F,counts)
    baseline=counts(old)
    chosen=('original',old)
    best=baseline
    for v in sorted({abs(a) for c in residual for a in c}):
        plan=layout(residual,v,component['condition'],component['components'],cap)
        cost=bill(plan)
        if all(a<=b for a,b in zip(cost,baseline)) and cost<best:
            chosen=('factored',v,plan)
            best=cost
    return chosen,best
~~~

Save the first listing as isofactor.py and the preceding component encoder as components.py. The following checks use the same prior frontend and parameter planner.

~~~~python
from itertools import product
from random import Random
from collections import Counter
import runpy
g=runpy.run_path('components.py');f=runpy.run_path('isofactor.py')
def sat(C,x):return all(any(x[abs(a)]==(a>0) for a in c) for c in C)
def oracle(C,b):
    n=max((abs(a) for c in C for a in c),default=0)
    return b if any(sat(C,dict(enumerate(bits,1))) for bits in product((0,1),repeat=n)) else 0
def read(C,b,w):
    assert sat(C,dict(enumerate(w,1)))
    return b
rng=Random(582);checks=0;unsat=0
for trial in range(64):
    F=g['clean']([tuple(rng.choice((-1,1))*rng.randrange(1,7) for _ in range(rng.randrange(1,4))) for j in range(3+trial%20)])
    plan=f['layout'](F,1,g['condition'],g['components'],8)
    yes=False
    for values in product((0,1),repeat=6):
        x=dict(enumerate(values,1))
        if sat(F,x):
            yes=True
            for b in (0,1):
                ct=f['encode'](plan,b,lambda:rng.randrange(2),oracle)
                assert f['decode'](plan,ct,x[1],x,read)==b
                checks+=1
    if not yes:
        unsat+=1
        # All independent share coins enumerated (unused suffix bits are harmless).
        h=len(plan[1])+sum(len(r or []) for r in plan[2])
        laws=[]
        for b in (0,1):
            law=Counter()
            for coins in product((0,1),repeat=h):
                it=iter(coins)
                law[repr(f['encode'](plan,b,lambda:next(it),oracle))]+=1
            laws.append(law)
        assert laws[0]==laws[1]
print(checks,unsat)
~~~~

~~~~python
import runpy
from pathlib import Path
from random import Random
from itertools import product
g=runpy.run_path('components.py')
front={}
s=Path('dag/Notes/pq-we-live-clause-matrix-product.md').read_text()
exec(s.split('~~~python\n')[1].split('def run_tests')[0],front)
from functools import lru_cache
clock={}
for name in ('pq-we-self-consistent-modulus','pq-we-ordered-radix-gadget'):
    for part in Path('dag/Notes/'+name+'.md').read_text().split('~~~python\n')[1:]:
        exec(part.split('~~~')[0],clock)
@lru_cache(None)
def shape(h,w):
    _,_,c=clock["select"](h,w,4,1021,48,8,16,4)
    m=c["m"]
    return c["payload"],c["Q"],(h-1)*4*m*m
def counts(t):
    tag=t[0]
    if tag in ('yes','no'):return (1,0,0)
    if tag=='leaf':
        C=t[1];vs=sorted({abs(a) for c in C for a in c});h=len(vs)
        ids={v:i+1 for i,v in enumerate(vs)}
        cs=[tuple(ids[abs(a)]*(1 if a>0 else -1) for a in c) for c in C]
        u,_=front['compile_program'](cs,h,0)
        return shape(h,len(u))
    vals=[counts(c) for c in (t[1] if tag=='and' else t[2])]
    return sum(v[0] for v in vals),sum(v[1] for v in vals),(sum if tag=='and' else max)(v[2] for v in vals)
def price(t):return counts(t)[0]
def sat(F,x):return all(any(x[abs(a)]==(a>0) for a in c) for c in F)
def oracle(C,b):
    vs=sorted({abs(a) for c in C for a in c})
    return b if any(sat(C,dict(zip(vs,v))) for v in product((0,1),repeat=len(vs))) else 0
def core(start,n,seed):
    rng=Random(seed);vs=list(range(start,start+n))
    return [tuple(i*(1 if rng.randrange(2) else -1) for i in rng.sample(vs,3)) for j in range(6*n)]
def conn(N,seed):
    F=core(2,N,seed)+core(2+N,N,seed+1)
    for j in range(6):
        for off in [2,2+N]:
            F.append((1 if j%2 else -1,off+j%N,-(off+(j+1)%N)))
    return F
f=runpy.run_path('isofactor.py')
def leaf(key):return counts(('leaf',key))
def bill(plan):
    maps,common,rem=plan
    if all(b is None for b in maps) or (not common and any(r==[] for r in rem)):return (1,0,0)
    tails=[] if any(r==[] for r in rem) else [r for r in rem if r is not None]
    cs=[leaf(k) for k in common];ts=[[leaf(k) for k in r] for r in tails]
    return (sum(x[0] for x in cs)+sum(x[0] for t in ts for x in t),
            sum(x[1] for x in cs)+sum(x[1] for t in ts for x in t),
            sum(x[2] for x in cs)+max((sum(x[2] for x in t) for t in ts),default=0))
def run(F):
    G,old=g['compile_tree'](F,counts)
    p=f['layout'](G,1,g['condition'],g['components'])
    before=[[leaf(f['canonical'](C)[0]) for C in g['components'](g['condition'](G,lit))] for lit in (-1,1)]
    normalized=(sum(x[0] for branch in before for x in branch),sum(x[1] for branch in before for x in branch),max(sum(x[2] for x in branch) for branch in before))
    print('normalized without factoring',normalized)
    print(len(G),old[0],len(p[1]),[len(r or []) for r in p[2]],counts(old),bill(p))
for n in [8,10]:run(conn(n,77))
def variant(C,off,b,index):
    out=[]
    for c in C:
        row=[]
        for lit in c:
            i=abs(lit)-1
            perm=(3*i+index+b)%8
            sign=(-1 if (i+index+b)%3==0 else 1)*(1 if lit>0 else -1)
            row.append(sign*(off+perm))
        out.append(tuple(row))
    return out
F=[]
for j,seed in enumerate([148,149,148,150]):
    for b in [0,1]:
        C=core(1,8,seed+(17 if j==3 and b else 0))
        for row in variant(C,2+8*j,b,j):
            F.append(tuple(row)+(1 if b==0 else -1,))
run(F)
assert f['select_plan'](F,g,counts,bill)[1]==(47140066888320,3229296,283609895744)
~~~~
