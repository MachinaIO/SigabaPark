---
title: Costed separator and component encryption after witness projection
refs: [definition:WE_CircuitSAT, note:pq-we-block-dominance, note:pq-we-ordered-radix-gadget, note:pq-we-contextual-interval-products]
tags: [witness-encryption, compilation, complexity, correctness]
---

The previous interval compiler kept almost all levels of the small NAND controls. This frontend moves the projection to the CNF, then chooses between a single tensor encoding and a tree of smaller independent encodings. It reuses the exact projection argument of the block-dominance note and [bounded variable elimination](https://www.cs.toronto.edu/~fbacchus/csc2512/Readings/EenBiere-SAT05.pdf). The contribution here is its combination with separator-conditioned, share-based tensor encryption and per-leaf modulus accounting.

**Exact projection.** For a pivot remove all clauses mentioning it and insert all nontautological positive-negative resolvents. An old witness restricts to a new witness. Conversely if a positive clause needs the pivot true and a negative one needs it false, their resolvent is violated. Hence every residual model lifts, including after successive pivots. The implementation skips pivots with more than 64 parent pairs, accepts residuals with no increase in clause count and bounds new resolvents after subsumption to width four. It makes a complete replacement or skips it. An empty CNF yields a certified YES; an empty clause yields a certified NO. Ordinary false-instance WE permits public YES encryption of the bit and public NO encryption of a constant. This shortcut does not provide witness extraction.

**Tree.** On disjoint variable components, SAT is the conjunction of component SAT. Secret-share the bit by XOR, encrypt one share per component with independent coins, and decrypt them all. For a connected residual also consider a public separator variable v: condition on each of its two values, split each residual by components, and encrypt the same bit in both branches. A valid witness selects its branch and restricts to the needed local assignments. Because the branches bind v and the components use disjoint remaining variables, independent local models in one branch combine to a global model. Each leaf compacts variables in a fixed public order and compiles its clauses as before. If the public statement or plan is not already available to Dec, its encoding and variable maps must be framed with the ciphertext. The prototype prices only leaf payloads.

On a fixed false AND, at least one child is false. Take all sibling shares uniform and put their parity XOR the message at that child. A reduction embeds its challenge there and samples every sibling with the original encoder; for fixed-message challenges complement the distinguisher output when the sibling parity is one to align the signed gap. Choosing a false child can use instance advice in a nonuniform or fixed-instance proof; a uniform reduction without such advice needs a separate selection argument. A false OR has two false branches, so the hybrid costs the sum of their distinguishing bounds. Each wrapper receives classical ciphertexts and can run a quantum distinguisher at the end. These arguments transfer the leaf hiding guarantees, with the indicated losses and simulation costs. For correctness add the errors of the AND children used by the actual witness, taking the worse branch at an OR. Budget leaves for both correctness and security before claiming end-to-end bits.

**Public selection and costs.** Consider a single component split or one conditioning pivot and the component splits below it; no recursively growing separator tree is needed. Compare against encrypting the same projected residual as one tensor program. In the three columns of the selection rule use total payload, total preimage-column count, and worst witness-path dense matrix multiply-adds. For an OR, sum the first two and take the maximum of the third. For an AND sum all three. Discard a candidate if any column exceeds the baseline; break ties lexicographically. Key setups, compilation, headers and traversal also need polynomial time and space. Counts of preimage columns are not encryption timings. Caps and a linear number of pivots keep planning polynomial if the leaf compiler and parameter selector are polynomial. For a security-matched implementation each candidate must meet its backend security parameter constraints before it is eligible.

**Controls.** Projection alone certified YES for all 60 seeded four-input five-NAND circuits used in the preceding comparison. They therefore use no lattice operations. On 120 other small CNFs, exhaustive assignment checks found 103 YES and 17 NO, matching the projected answer in every case. An ideal SAT leaf oracle exercised valid decryptions; an exact mask enumeration separately checked the false OR-of-AND share distributions.

On a connected residual of 102 clauses formed from two eight-variable cores and a common separator, fixed k=32 and n=4 made the split more expensive in preimage-column count, so the three-metric rule retained the monolithic plan. Recomputing the modulus and matrix width for each leaf with the preceding correctness planner (n=4, p=1021, S=8, E=16, planner precision 48, radix 16) selected an OR split. Monolithic and split payloads were 468702373268880 and 27760782629440 bits respectively. Preimage columns fell from 4966740 to 2459192 and worst-path multiply-adds from 1644567081840 to 120595730944. At four eight-variable cores the corresponding counts were 9127223035618480 versus 51383590424640 bits, 21644324 versus 4685296 columns, and 16154371083344 versus 228526001440 multiply-adds. These are accounting controls on generated formulas, not cryptographic benchmarks or evidence that the cores are hard to decide. The advantage depends on the ability to use smaller moduli for shorter independent components. A lattice hardness floor could alter these choices; 48 here is a planner input and is not an established secrecy or full correctness level.

~~~python
def clean(F):
    rows={frozenset(c) for c in F if not any(-a in c for a in c)}
    keep=[]
    for c in sorted(rows,key=lambda x:(len(x),tuple(sorted(x)))):
        if not any(k<=c for k in keep):
            keep.append(c)
    return tuple(keep)

def eliminate(F,width=4,pairs=64):
    F=clean(F)
    while F and F[0]:
        best=None
        for v in sorted({abs(x) for c in F for x in c}):
            pos=[c for c in F if v in c];neg=[c for c in F if -v in c]
            if len(pos)*len(neg)>pairs:
                continue
            union=clean((a|b)-{v,-v} for a in pos for b in neg)
            if any(len(c)>width for c in union):
                continue
            kept=[c for c in F if v not in c and -v not in c]
            G=clean(kept+list(union))
            if len(G)>len(F):
                continue
            score=(len(G),sum(map(len,G)),v)
            if best is None or score<best[0]:
                best=score,G
        if best is None:
            break
        F=best[1]
    return F

def components(F):
    pending=list(F);groups=[]
    while pending:
        stack=[pending.pop()];group=[]
        while stack:
            c=stack.pop();group.append(c)
            vs={abs(a) for a in c}
            remaining=[]
            for d in pending:
                if any(abs(a) in vs for a in d):
                    stack.append(d)
                else:
                    remaining.append(d)
            pending=remaining
        groups.append(tuple(group))
    return groups

def and_plan(F):
    if not F:return ('yes',)
    if not F[0]:return ('no',)
    leaves=[('leaf',C) for C in components(F)]
    return ('and',leaves) if len(leaves)>1 else leaves[0]

def condition(F,lit):
    return clean(c-{-lit} for c in F if lit not in c)

def compile_tree(F,counts):
    F=eliminate(F)
    base=and_plan(F)
    if base[0] in ('yes','no'):
        return F,base
    single=('leaf',F)
    baseline=counts(single)
    def eligible(cost):return all(a<=b for a,b in zip(cost,baseline))
    best=base if eligible(counts(base)) else single
    budget=counts(best)
    if base[0]=='and':return F,best
    for v in sorted({abs(a) for c in F for a in c}):
        branches=[condition(F,lit) for lit in (-v,v)]
        parts=[and_plan(G) for G in branches]
        if not any(p[0]=='and' for p in parts):
            continue
        plan=('or',v,parts)
        cost=counts(plan)
        if eligible(cost) and cost<budget:
            best,budget=plan,cost
    return F,best

def encrypt_tree(node,bit,randbit,leaf_enc):
    tag=node[0]
    if tag=='no':return 0
    if tag=='yes':return bit
    if tag=='leaf':return leaf_enc(node[1],bit)
    if tag=='or':
        return [encrypt_tree(c,bit,randbit,leaf_enc) for c in node[2]]
    shares=[randbit() for _ in node[1][1:]]
    last=bit
    for s in shares:last^=s
    return [encrypt_tree(c,s,randbit,leaf_enc) for c,s in zip(node[1],shares+[last])]

def decrypt_tree(node,ct,assignment,leaf_dec):
    tag=node[0]
    if tag in ('yes','no'):return ct
    if tag=='leaf':return leaf_dec(node[1],ct,assignment)
    if tag=='or':
        b=int(assignment[node[1]])
        return decrypt_tree(node[2][b],ct[b],assignment,leaf_dec)
    answer=0
    for c,v in zip(node[1],ct):answer^=decrypt_tree(c,v,assignment,leaf_dec)
    return answer
~~~

Save the first listing as components.py and run this control from the DAG repository root.

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
rng=Random(916);yes=no=0
for trial in range(120):
    n=5;F=[tuple(rng.choice((-1,1))*rng.randrange(1,n+1) for _ in range(3)) for j in range(trial%26)]
    G,t=g['compile_tree'](F,counts)
    witness=False
    for vals in product((0,1),repeat=n):
        x=dict(zip(range(1,n+1),vals))
        if sat(F,x):
            witness=True
            assert sat(G,x)
            for b in (0,1):
                ct=g['encrypt_tree'](t,b,lambda:rng.randrange(2),oracle)
                assert g['decrypt_tree'](t,ct,x,lambda C,v,a:v)==b
    assert witness==bool(oracle(G,1))
    if witness:yes+=1
    else:no+=1
print('random YES/NO',yes,no)
for N in [6,8,10]:
    F=conn(N,77)
    G,t=g['compile_tree'](F,counts)
    print(N,len(G),t[0],(counts(('leaf',G)) if G and G[0] else (1,0,0)),counts(t))

for blocks in [3,4]:
    N=8
    F=[]
    for j in range(blocks):
        off=2+j*N
        F.extend(core(off,N,148+j))
        F.extend((1 if k%2 else -1,off+k,-(off+k+1)) for k in range(6))
    G,t=g['compile_tree'](F,counts)
    print('blocks',blocks,len(G),t[0],counts(('leaf',G)),counts(t))
rng=Random(712)
modes={}
for _ in range(60):
    F=front['nand_cnf'](4,[(rng.randrange(5+j),rng.randrange(5+j)) for j in range(5)])
    _,t=g['compile_tree'](F,counts)
    modes[t[0]]=modes.get(t[0],0)+1
print('NAND modes',modes)
# Check every mask combination at a false OR of two conjunctions.
from collections import Counter
plan=('or',1,[('and',[('leaf',True),('leaf',False)]),('and',[('leaf',False),('leaf',True)])])
laws=[]
for bit in (0,1):
    law=Counter()
    for tape in product((0,1),repeat=2):
        rand=iter(tape)
        out=g['encrypt_tree'](plan,bit,lambda:next(rand),lambda valid,b:b if valid else 0)
        law[tuple(tuple(row) for row in out)]+=1
    laws.append(law)
assert laws[0]==laws[1]
~~~~
