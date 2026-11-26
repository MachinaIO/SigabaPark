---
title: Witness encryption from binary inner-product predicates across a circuit cut
refs: [definition:WE_CircuitSAT, note:pq-we-split-witness-abe, theorem:AdvancedEncryption.WE.IPE.cover_dot_zero_iff, theorem:AdvancedEncryption.WE.IPE.binary_digit_projection]
tags: [circuit-sat, witness-encryption, predicate-encryption, lwe]
---

PR #85 reduces the numbers of entries in a split-witness construction but the sampled key needed a depth-835 NAND policy. Here the cryptographic terminal test has just one modular inner product. The construction uses the zero-inner-product predicate encryption of [Agrawal, Freeman and Vaikuntanathan (AFV), Sections 2 and 4](https://theory.stanford.edu/~dfreeman/papers/FuncEnc.pdf) and the split-witness idea of [BJKPW](https://eprint.iacr.org/2017/874.pdf). Plain decision LWE is the underlying AFV assumption. A quantitative secure parameter set for the registered WE machine remains open.

**Compile the incompatibility relation.** Split the original witness coordinates into two disjoint sets. On an exact CNF, require the left and right partial assignments to satisfy their respective purely local clauses. For each crossing clause, form an edge between its left and right subclauses. An endpoint is active when every literal in its subclause is false. A joint witness satisfies the crossing clauses iff there is no edge between active endpoints. Duplicate edges and tautologies can be dropped. This also works when the literals denote arbitrary efficiently computable functions of just one party's input.

Cover the edge relation exactly by p complete bipartite rectangles. For each rectangle i, the binary key vector v has bit i set iff any of its left endpoints is active; the binary attribute w analogously summarizes the right side. Then the integer inner product counts rectangles witnessing a violation. Over a prime modulus q>p it is zero exactly for accepting pairs. Overlap of rectangles is harmless. The Lean proof cover_dot_zero_iff establishes this equivalence, including empty covers, for any modulus greater than p. The prime choice also makes every nonzero score a unit for the cryptographic route. An inexpensive cover is obtained by maximum bipartite matching and a minimum vertex cover: assign each edge to a selected endpoint and gather the assigned edges into one star per endpoint. This minimizes the number of stars, without claiming optimality over arbitrary rectangles. With ordinary width-three clauses every crossing edge has a singleton subclause, hence all signed singleton literals already give a cover of size at most 2n. The code uses the smaller computed cover.

**Ordinary WE.** Use one fresh AFV master setup per encryption. Issue one key for each locally admissible left assignment, fixing its actual Boolean predicate vector. Encrypt the message bit once for each locally admissible right assignment, with its actual Boolean attribute. The known witness selects both entries. On a false statement every such pair has nonzero inner product. If either side is empty, a public fixed-zero mode suffices. Empty or singleton vector dimensions may be padded with zero coordinates to meet the PE interface. On a challenge entry, choose the same public attribute for both AFV challenges before setup, request only rejecting keys and use the challenge public parameters to generate all companion entries. This fits the weak selective attribute-hiding game (AFV Def. 2.2, Remark 2.3, Thm. 4.2). It needs no attribute privacy between different labels. The exponential numbers of entries, key queries, statistical errors and public enumeration work must be charged to a concrete reduction. A polynomial-time asymptotic theorem alone cannot certify this parameter regime or the quantum machine game.

**Remove all higher gadget digits.** AFV writes the predicate coefficients in binary to form the key matrix and to combine ciphertext vectors at decryption. Every coefficient in the present compiler is 0 or 1. Use only digit zero of each coordinate. Start with the full AFV setup and ciphertext and project away the higher digit matrices and higher digit ciphertext vectors. With the same full coins, the restricted-key matrix and the decrypted bit are exactly unchanged. The Lean theorem binary_digit_projection proves the common accumulator identity for both matrices and ciphertext vectors in any additive commutative monoid. The retained setup matrices are sampled independently; in encryption keep the shared secret, base error and blinding matrix and sample only the retained independent sign matrices. This realizes the marginal law exactly. A reduction can project an ordinary AFV challenge, so this omission introduces no new assumption or hybrid. In the conservative analysis keep the full scheme's parameter requirements. Structurally, at AFV matrix width m, one ciphertext now has **1+(1+p)m residues** rather than 1+[1+p(1+floor(log2 q))]m. A functional key is still a short vector with 2m integer coordinates; its predicate label can be recomputed. One fresh setup retains 1+p public n_LWE by m matrices and a target vector. AFV decryption needs the label and public parameter dimensions; it does not perform the original circuit gate evaluations.

A further per-selected-key correctness calculation follows directly from AFV Eq. (4.3). With centered noise lifts x (base vector), e1,e2 (halves of the independently generated secret key), and x' (scalar error), the residual signed random term is a sum of independent Rademacher signs times e2_j x_k, repeated over the h=wt(v) retained coordinates. Conditional on x,e1,e2,x' its variance is h||e2||²||x||². The inequality cosh(t)≤exp(t²/2) and the exponential moment bound give absolute error at most

    |x'| + ||e1|| ||x|| + sqrt(2 h ln(2/eps)) ||e2|| ||x||

except with probability eps. Handle h=0 directly. For p=117 and eps=2^-129 the multiplier on ||e2|| ||x|| is at most 145.21. To use this as a finite correctness proof, bound the joint norm-tail probability by another 2^-129 and require the displayed result below q/4 with rounding slack. Norm thresholds, discrete sampling and a concrete LWE cost are still needed; the multiplier alone is not a security estimate.

**Computable local table indices.** For ordinary CNF on disjoint input variables, count each local formula by eliminating variables in increasing current neighborhood size and summing products of local factors. Store the two unsummed counts for the chosen variable conditional on its neighboring later variables. In reverse elimination order, let N be the remaining completions under the fixed later bits; if the two counts are a,b, exactly N·a/(a+b) completions have next bit zero. All other conditioned factors give the same multiplier to either bit. Skipping the zero interval ranks a given witness, and comparing with its length unranks a table index. This supports sequential table generation with no invalid rows. Local elimination can itself be exponential in its induced width. We use exact integer arithmetic and switch from uint64 to arbitrary precision before a possible overflow. Distinct assignments can yield the same profile; the reported main counts include all admissible assignments. Optional profile deduplication or deletion of bitwise supersets is sound for ordinary WE if the decryptor can map to a retained subset. The cost of discovering that map must be included.

**Full-size measurements.** Use the planted 300-clause, 128-input formula of PR #85, whose source compiler emits exactly 4,096 NAND gates. For the original contiguous split with 64 inputs per side, there are 221 distinct crossing edges and 151 stars. In the earlier eight-clause contradiction variant these numbers are 213 and 147. The table below is for the planted instance. The second partition uses balanced input swaps that increase the smaller local clause count or break ties using the total. For rows three to six move one variable per step using a simple independent-clause score; the displayed counts use exact elimination, not that score. The last column counts log2(2K+(1+p)C), the leading coefficient of m in total key-plus-ciphertext scalar slots. Short key coefficients and modulus-q residues can have different byte costs. Setup, final ciphertext scalars, public preprocessing and runtime are excluded.

| Inputs on key side | Stars p | Keys K | Attribute ciphertexts C | log2 leading slots |
|---|---:|---:|---:|---:|
| 64 contiguous | 151 | 119199844245479424 | 120686712862299136 | 64.011 |
| 64 balanced heuristic | 118 | 1260497754834880 | 469599608124643 | 55.697 |
| 65 | 116 | 2168424367659088 | 272220811881062 | 55.006 |
| 66 | 119 | 4336848735318176 | 163899730812838 | 54.654 |
| 67 | 117 | 5569680682508448 | 114163505439814 | 54.450 |
| 68 | 117 | 7918500966777728 | 77310362011450 | 54.470 |

For the 67/61 split, the projected AFV ciphertext has 118m+1 residues per entry and the single-challenge floor in #64 is ceil(128+2 log2 C)=222 bits before reduction inflation. The table is enormous. It trades more entries than the repair code in #85 for a much simpler cryptographic predicate. No end-to-end timing advantage over either #85 or the Ring-LWE BGG+ scheme in #83 has been established. Two independent model counters (component-cached branching and variable elimination) agreed on both 64/64 rows. The reference below uses variable elimination, with induced widths 8/6 and 22/23 respectively for its specified tie order. Both ranking directions were tested on the planted witness and sampled indices. The full key and ciphertext tables were not materialized.

**Reduce entries while keeping the same 117-coordinate predicate.** On the 67/61 cut, two inputs per side do not appear in any crossing endpoint. Eliminate them existentially from the local clauses by resolution: for a variable x keep clauses not mentioning it and add all non-tautological resolvents between its positive and negative clauses. For any assignment to the surviving variables, these conditions are necessary and sufficient for some choice of x. A public cap on resolution growth can revert to the unprojected calculation. Rank just the extendible surviving assignments by the same exact local index. This gives 1,799,247,130,578,720 keys and 66,019,523,484,510 ciphertexts.

Further replace any crossing subclause t that contains a variable used by no other crossing subclause (and t is not a singleton) with a new bit indicating that all its literals are false. Include the local defining equivalence, then existentially eliminate these single-use original variables and the purely local variables. Retain the other raw boundary bits. A witness computes each flag directly. Every locally admitted tuple of remaining bits and flags has an original local extension, and all crossing coordinates depend only on the retained tuple. Combining extensions on disjoint sides proves soundness. The flags are computed before PE evaluation, so this changes table lengths without increasing the predicate dimension or encrypted circuit depth.

| 67/61 split | Keys | Ciphertexts | Predicate dimension |
|---|---:|---:|---:|
| All locally admissible assignments | 5,569,680,682,508,448 | 114,163,505,439,814 | 117 |
| Remove private inputs | 1,799,247,130,578,720 | 66,019,523,484,510 | 117 |
| Remove private and single-use inputs | **570,808,747,385,608** | **41,923,871,289,682** | **117** |

The last row introduces five flags on the left and three on the right. Its local elimination widths are 23 and 25. The key and ciphertext exponents are respectively 49.02 and 45.25. The squared-advantage single-challenge floor becomes 219 bits before reduction costs. These are counts of extendible labels on a planted YES control. The WE false-statement game is played on NO inputs. To use the 219-bit arithmetic floor uniformly on this branch, decide from public data whether the ciphertext count is at most 41,923,871,289,682 (and whether resource caps for dimension, key count and preprocessing hold). Use this PE branch only when its caps pass; otherwise dispatch to a separately analyzed scheme. The branch selection is message-independent. The NO cases of the fallback require their own security and clock bounds. The YES measurement by itself gives no uniform LWE parameter claim. The reference checks the projected label sets against explicit images on small inputs.

**General NANDs and a separation control.** From a raw NAND list, normalize forward reads to true. Determine which gates depend solely on left, right or constant wires. Treat each side-local gate as an opaque, locally evaluated Boolean atom, which does not increase witness length. Distribute the remaining gates to CNF over those atoms only while an explicit size cap permits. If the output polarity overflows, retain truth values of mixed gates in its dependency cone as extra witness bits; enforce each named NAND by its two binary implications and one ternary implication and require the output. Local atoms are always evaluated on actual inputs, never guessed. A satisfying original input extends by recording its mixed gate values; conversely the clauses force the unique correct values in gate order. The augmented bits may be partitioned between the two sides before the same cover compiler. This fallback can add as many bits as there are mixed gates; revert to the original #64 split when the added cost is excessive. The local model counter above applies directly to clauses on input variables; local restrictions involving opaque functions require enumeration or another counting algorithm.

A second 128-input/4,096-gate family tests the opaque route. Each side emits 16 parities of disjoint four-bit groups; 48 crossing NAND guards forbid adjacent parity pairs in a three-regular bipartite graph. Compilation produced 16 star coordinates and zero additional witnesses. This function has no width-three CNF on the original inputs: every partial assignment on at most three input bits can extend to all-even right parities, yet some full assignments violate a guard. A nontrivial width-three clause implied by the function would contradict the first fact. The inputs contain deliberately redundant padding and the parity system is easy; public enumeration of the two 16-bit profile domains already provides an assumption-free alternative. More generally at small p, a subset-zeta table on the p-bit masks can test for a compatible pair in O(p·2^p) Boolean operations after enumerating profiles. Cryptographic gains require comparison with such public solvers.

**Reproduction.** Python 3 with NumPy. The truth-table checks cover 300 small CNFs, all local pairings in a 16-variable example, and raw gate lists including default-true forward reads and auxiliaries. The public-seed control is for reproducibility. A separate arithmetic test compares the full and projected ciphertext-vector and public-matrix accumulators on shared coins for all 128 predicates of a seven-coordinate toy example. It does not generate trapdoor keys, instantiate secure parameters, or materialize the WE tables.

~~~python
from itertools import product
from random import Random
from collections import defaultdict

def fails(side,x):
    return all((x>>(abs(v)-1)&1)!=(v>0) for v in side)

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

def profile(cover,x,side):
    return sum(any(fails(vs,x) for vs in pair[side])<<j for j,pair in enumerate(cover))

def check(n,F,L,seq):
    loc,edges,cover=compile_cnf(n,F,L)
    for x in seq:
        out=not any(fails(c,x) for rows in loc for c in rows)
        dot=(profile(cover,x,0)&profile(cover,x,1)).bit_count()
        assert (out and dot==0)==(not any(fails(c,x) for c in F))
    return len(loc[0]),len(loc[1]),len(edges),len(cover)

# Differential truth tables, including empty and wide clauses, duplicates and tautologies.
r=Random(861)
for _ in range(300):
    n=r.randrange(1,8)
    F=[tuple(r.choice((-1,1))*r.randint(1,n) for _ in range(r.randrange(6)))
       for j in range(r.randrange(12))]
    L={i+1 for i in range(n) if r.randrange(2)}
    check(n,F,L,range(1<<n))

# Match the planted input generator from PR #85 (300 source clauses, 4096 NANDs).
r=Random(851)
n=128;w=r.getrandbits(128);F=[]
for _ in range(300):
    vs=r.sample(range(1,n+1),3)
    row=[v if r.randrange(2) else -v for v in vs]
    if fails(row,w):row[0]*=-1
    F.append(row)
seq=[w]+[r.getrandbits(128) for _ in range(300)]
for no in (False,True):
    rows=F.copy()
    if no:rows[:8]=[[(i+1)*(1 if t else -1) for i,t in enumerate(bits)] for bits in product(range(2),repeat=3)]
    print('UNSAT' if no else 'SAT',check(128,rows,set(range(1,65)),seq))

# Fixed characteristic dimension: actual tables can be smaller than 2^64.
# Eight variables per side, exhaustive local admissibility and both cross profiles.
n=16;L=set(range(1,9))
rows=[(i,i+1) for i in range(1,8)]+[(-i,-i-1) for i in range(9,16)]
rows += [(i,-(8+i)) for i in range(1,9)]+[(-i,8+i) for i in range(1,9)]
loc,edges,cover=compile_cnf(n,rows,L)
profiles=[]
for side in (0,1):
    vals=[u<<(8*side) for u in range(256)]
    ps={profile(cover,x,side) for x in vals if not any(fails(c,x) for c in loc[side])}
    profiles.append(ps)
def minimal(ps):return {p for p in ps if not any(q!=p and q&p==q for q in ps)}
direct=sum(not any(fails(c,x) for c in rows) for x in range(65536))
pairs=sum((a&b)==0 for a in profiles[0] for b in profiles[1])
assert direct==pairs==2
print('small states',len(cover),[(len(p),len(minimal(p))) for p in profiles],direct)

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

import numpy as np
from math import prod

class LocalIndex:
    """Exact model count and reversible enumeration; with checked integer width."""
    def __init__(self,vs,clauses):
        vs=set(vs)

        self.steps=[]
        factors=[]
        self.width=0
        const=1
        for c in clauses:
            ax=tuple(sorted(set(map(abs,c))))
            if not ax:
                const=0
                continue
            table=np.ones((2,)*len(ax),dtype=np.uint64)
            table[tuple(int(-i in c) for i in ax)]=0
            factors.append((ax,table))
        while vs:
            near={i:set() for i in vs}
            for ax,_ in factors:
                for i in ax:near[i].update(ax)
            i=min(vs,key=lambda i:(len(near[i]),i))
            vs.remove(i)
            use=[p for p in factors if i in p[0]]
            factors=[p for p in factors if i not in p[0]]
            ax=tuple(sorted(near[i]|{i}))
            self.width=max(self.width,len(ax)-1)
            t=np.ones((2,)*len(ax),dtype=np.uint64)
            for scope,f in use:
                if f.dtype==object or int(t.max())*int(f.max())>=1<<64:
                    t=t.astype(object)
                t*=f.reshape(tuple(2 if j in scope else 1 for j in ax))
            k=ax.index(i)
            self.steps.append((i,ax,k,t))
            if len(ax)==1:
                const*=int(t[0])+int(t[1])
            else:
                if int(t.max())>=1<<63:t=t.astype(object)
                factors.append((ax[:k]+ax[k+1:],t.sum(axis=k)))
        self.total=const
    def convert(self,value,decode):
        count=self.total
        assert count>0
        if decode:
            assert 0<=value<count
        x=0 if decode else value
        rank=0
        for i,ax,k,t in reversed(self.steps):
            idx=[x>>(j-1)&1 for j in ax]
            idx[k]=0;a=int(t[tuple(idx)])
            idx[k]=1;b=int(t[tuple(idx)])
            assert a+b>0 and count*a%(a+b)==0
            low=count*a//(a+b)
            one=value>=low if decode else (x>>(i-1)&1)
            if one:
                rank+=low
                if decode:value-=low
                x|=1<<(i-1)
                count-=low
            else:count=low
            assert count>0
        assert count==1
        return x if decode else rank

# Both complete table counts from independently implemented variable elimination.
for label,L in [('natural',set(range(1,65))),('heuristic',improve(F))]:
    loc,edges,cover=compile_cnf(128,F,L)
    counts=[]
    for side,vs in enumerate((L,set(range(1,129))-L)):
        index=LocalIndex(vs,loc[side])
        counts.append(index.total)
        for j in [0,index.total-1]+[r.randrange(index.total) for _ in range(30)]:
            x=index.convert(j,True)
            assert index.convert(x,False)==j and not any(fails(c,x) for c in loc[side])
        masked=w&sum(1<<(v-1) for v in vs)
        assert index.convert(index.convert(masked,False),True)==masked
        print(label,side,'width',index.width,'entries',index.total)
    assert counts==([119199844245479424,120686712862299136] if label=='natural'
                    else [1260497754834880,469599608124643])
from math import log2
def weighted(p,counts):
    K,C=counts
    return 2*K+(1+p)*C
L=improve(F)
den=set(range(1,129))
for t in range(1,5):
    def estimate(L):
        loc,edges,cover=compile_cnf(128,F,L)
        k,c=(len(loc[0]),len(loc[1]))
        return 2*2**len(L)*(7/8)**k+(len(cover)+1)*2**(128-len(L))*(7/8)**c
    v=min(sorted(den-L),key=lambda v:estimate(L|{v}))
    L=L|{v}
    loc,edges,cover=compile_cnf(128,F,L)
    counts=[]
    for vs,cl in zip((L,den-L),loc):
        idx=LocalIndex(vs,cl)
        mask=w&sum(1<<(i-1) for i in vs)
        assert idx.convert(idx.convert(mask,False),True)==mask
        counts.append(idx.total)
    print('weighted',len(L),v,len(cover),counts,round(log2(weighted(len(cover),counts)),3))

def boundary_cnf(n,g,L,cap=8192):
    # Each local gate is an opaque atom with a known owner. Keep complemented
    # expressions as CNF over those atoms; introduce a definitional bit on overflow.
    const, left, right = 0,1,2
    own={0:const,**{i:left if i in L else right for i in range(1,n+1)}}
    clauses=[]
    aux=[]
    atom=lambda v:(((v,),),((-v,),))
    table={0:((),((),)),**{i:atom(i) for i in range(1,n+1)}}
    # Anchor the definition clauses to signed wire names; mixed operands of
    # materialized gates must themselves have names with enforced definitions.
    normalized={}
    named=set(range(n+1))
    def ensure(v):
        pending=[(v,False)]
        while pending:
            t,ready=pending.pop()
            if t in named:continue
            a,b=normalized[t]
            if ready:add_def(t,a,b)
            else:pending.extend(((t,True),(a,False),(b,False)))
    def add_def(v,a,b):
        if v in named:return
        named.add(v);aux.append(v)
        # 0 is true in the wire language; remove it during normalization below.
        for literals in (((a,1),(v,1)),((b,1),(v,1)),((a,-1),(b,-1),(v,-1))):
            if any(own[i]==const and (table[i][0]==())==(sg==1) for i,sg in literals):continue
            row={i*sg for i,sg in literals if own[i]!=const}
            if not any(-i in row for i in row):clauses.append(tuple(sorted(row)))
    def norm(rows):
        return tuple(sorted(set(rows))) if len(rows)<=cap else None
    def union(f,h):
        if f==((),) or h==((),):return ((),)
        if f is None or h is None:return None
        return norm(f+h)
    def distrib(f,h):
        if f==() or h==():return ()
        if f is None or h is None or len(f)*len(h)>cap:return None
        out=set()
        for u in f:
            for v in h:
                z=set(u)|set(v)
                if not any(-i in z for i in z):out.add(tuple(sorted(z)))
        return tuple(sorted(out))
    for j,(a,b) in enumerate(g):
        v=n+1+j
        a=a if a<v else 0;b=b if b<v else 0
        normalized[v]=a,b
        own[v]=own[b] if own[a]==const else own[a] if own[b]==const or own[a]==own[b] else 3
        if own[v] in (left,right):
            # Preserve a literal through negations to expose repeated endpoints.
            table[v]=(table[a][1],table[a][0]) if a==b else atom(v)
            named.add(v)
        elif own[v]==const:
            t=not (table[a][0]==() and table[b][0]==())
            table[v]=((),((),)) if t else (((),),())
            # A constant-only actual wire may appear in a named gate definition.
            named.add(v)
        elif a==b:
            table[v]=table[a][1],table[a][0]
        else:
            pos=distrib(table[a][1],table[b][1])
            neg=union(table[a][0],table[b][0])
            table[v]=pos,neg
    out=n+len(g) if g else 0
    result=table[out][0]
    if result is None:
        ensure(out);result=((out,),)
    return clauses+list(result),own,aux

def opaque_demo():
    n=128;L=set(range(1,65));g=[]
    def nand(a,b):
        g.append((a,b));return n+len(g)
    def xor(a,b):
        t=nand(a,b);return nand(nand(a,t),nand(b,t))
    def both(a,b):
        t=nand(a,b);return nand(t,t)
    v=[]
    for j in range(32):
        a=1+4*j
        v.append(xor(xor(a,a+1),xor(a+2,a+3)))
    edges=[(i,(i+j)%16) for i in range(16) for j in (0,1,5)]
    guards=[nand(v[i],v[16+j]) for i,j in edges]
    while len(g)<4096-2*(len(guards)-1):nand(0,0)
    t=guards[0]
    for guard in guards[1:]:t=both(t,guard)
    assert len(g)==4096
    return L,g

def values(n,g,x):
    w=[True]+[bool(x>>(i-1)&1) for i in range(1,n+1)]
    for a,b in g:
        w.append(not ((w[a] if a<len(w) else True) and (w[b] if b<len(w) else True)))
    return w

def validate(n,g,L,cap,samples):
    fs,own,aux=boundary_cnf(n,g,L,cap)
    # True constants are evaluated locally. Auxiliary ownership is arbitrary.
    ll={i for i,s in own.items() if s in (0,1)}|set(aux[::2])
    loc,edges,cover=compile_cnf(n+len(g),fs,ll)
    for x in samples:
        vals=values(n,g,x)
        z=sum(1<<(i-1) for i,b in enumerate(vals[1:],1) if b)
        def accept(a):
            return not any(fails(c,a) for side in loc for c in side) and not (
                profile(cover,a,0)&profile(cover,a,1))
        assert accept(z)==(vals[-1] if g else True)
        if len(aux)<=8 and n<=5:
            assert any(accept((z & ~sum(1<<(i-1) for i in aux))|
                        sum((h>>k&1)<<(i-1) for k,i in enumerate(aux)))
                       for h in range(1<<len(aux)))==(vals[-1] if g else True)
    return len(edges),len(cover),len(aux)

L,g=opaque_demo()
print('opaque',validate(128,g,L,8192,[0,1|(1<<64)]+[r.getrandbits(128) for _ in range(30)]))
for _ in range(80):
    n=r.randrange(1,6);s=r.randrange(8)
    g=[(r.randrange(n+s+1),r.randrange(n+s+1)) for j in range(s)]
    validate(n,g,set(range(1,n//2+1)),r.choice((1,2,8)),range(1<<n))
# This 4-input mixed circuit exceeds a one-clause distribution cap.
mixed=[(1,3),(2,4),(5,6),(7,7)]
fallback=validate(4,mixed,{1,2},1,range(16))
assert fallback[-1]>0
print('named mixed-gate fallback:',fallback)
# Check equality of full and projected AFV accumulators on common coins.
# Arithmetic only: no key sampler, parameter selection, or security experiment.
def check_digit_projection():
    rng=np.random.default_rng(88)
    q=257;p=7;m=5;n=3;k=q.bit_length()-1
    A=rng.integers(q,size=(p,k+1,n,m),dtype=np.int64)
    B=rng.integers(q,size=(n,m),dtype=np.int64)
    secret=rng.integers(q,size=n,dtype=np.int64)
    noise=rng.integers(-2,3,size=m,dtype=np.int64)
    w=rng.integers(2,size=p,dtype=np.int64)
    Rs=2*rng.integers(2,size=(p,k+1,m,m),dtype=np.int64)-1
    def block(i,j):
        return ((A[i,j]+(1<<j)*int(w[i])*B).T@secret+Rs[i,j].T@noise)%q
    full=np.array([[block(i,j) for j in range(k+1)] for i in range(p)])
    short=np.array([block(i,0) for i in range(p)])
    for mask in range(1<<p):
        v=np.array([mask>>i&1 for i in range(p)],dtype=np.int64)
        bits=np.array([(v>>j)&1 for j in range(k+1)]).T
        assert np.array_equal((full*bits[:,:,None]).sum(axis=(0,1))%q,(short*v[:,None]).sum(axis=0)%q)
        assert np.array_equal((A*bits[:,:,None,None]).sum(axis=(0,1))%q,(A[:,0]*v[:,None,None]).sum(axis=0)%q)
    print('full/projected matrix and ciphertext sums: 128 predicates')
check_digit_projection()

def forget(clauses,private,cap=10000):
    cs=set(clauses)
    for i in sorted(private):
        pos=[row for row in cs if i in row]
        neg=[row for row in cs if -i in row]
        if len(pos)*len(neg)>cap:raise OverflowError
        cs={row for row in cs if i not in row and -i not in row}
        for a in pos:
            for b in neg:
                row=(set(a)|set(b))-{i,-i}
                if not any(-v in row for v in row):cs.add(tuple(sorted(row)))
        if len(cs)>cap:raise OverflowError
    return tuple(sorted(cs))

for _ in range(100):
    vs=set(range(1,8))
    cs=[tuple(sorted(v if r.getrandbits(1) else -v for v in r.sample(sorted(vs),3))) for j in range(10)]
    private=set(r.sample(sorted(vs),3))
    projected=forget(cs,private)
    mask=sum(1<<(v-1) for v in vs-private)
    original={x&mask for x in range(128) if not any(fails(c,x) for c in cs)}
    assert original=={x&mask for x in range(128) if not any(fails(c,x) for c in projected)}

def projected_tally(L):
    loc,edges,cover=compile_cnf(128,F,L)
    counts=[]
    for side,vs in enumerate((L,set(range(1,129))-L)):
        exposed={abs(v) for term in cover for row in term[side] for v in row}
        cs=forget(loc[side],vs-exposed)
        index=LocalIndex(exposed,cs)
        counts.append(index.total)
        x=w&sum(1<<(v-1) for v in exposed)
        assert index.convert(index.convert(x,False),True)==x
    return counts
L=improve(F)
for v in (12,76,36):L.add(v)
pc=projected_tally(L)
print('projected 67/61',pc,[round(log2(v),3) for v in pc])

def leaf_basis(vs,local,ends,x):
    incidence={v:[t for t in ends if any(abs(i)==v for i in t)] for v in vs}
    hidden={v for v,ts in incidence.items() if not ts or len(ts)==1 and len(ts[0])>1}
    flags={t:i+129 for i,t in enumerate(sorted(t for t in ends if any(abs(v) in hidden for v in t)))}
    cs=list(local)
    for t,h in flags.items():
        cs.extend(tuple(sorted((-h,-v))) for v in t)
        cs.append(tuple(sorted((h,)+t)))
    exposed=(vs-hidden)|set(flags.values())
    z=(x&sum(1<<(i-1) for i in vs-hidden))|sum(int(fails(t,x))<<(h-1) for t,h in flags.items())
    return exposed,forget(cs,hidden),z,flags

loc,edges,cover=compile_cnf(128,F,L)
for side,vs in enumerate((L,set(range(1,129))-L)):
    ends={e[side] for e in edges}
    exposed,cs,z,flags=leaf_basis(vs,loc[side],ends,w)
    idx=LocalIndex(exposed,cs)
    assert idx.convert(idx.convert(z,False),True)==z
    for pair in cover:
        actual=any(fails(t,w) for t in pair[side])
        revised=any((z>>(flags[t]-1)&1) if t in flags else fails(t,z) for t in pair[side])
        assert bool(revised)==actual
    print('leaf projection',side,len(flags),idx.width,idx.total,round(log2(idx.total),3))
for _ in range(60):
    vs=set(range(1,8))
    def clause(k):
        return tuple(sorted(i if r.getrandbits(1) else -i for i in r.sample(sorted(vs),k)))
    local=[clause(3) for _ in range(5)]
    ends={clause(r.choice((1,2))) for _ in range(6)}
    exposed,cs,_,flags=leaf_basis(vs,local,ends,0)
    ix=LocalIndex(exposed,cs)
    keep=exposed-set(flags.values())
    def pack(x):
        return (x&sum(1<<(i-1) for i in keep))|sum(int(fails(t,x))<<(h-1) for t,h in flags.items())
    image={pack(x) for x in range(128) if not any(fails(t,x) for t in local)}
    assert image=={ix.convert(j,True) for j in range(ix.total)}
~~~
