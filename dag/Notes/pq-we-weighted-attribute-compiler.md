---
title: Shortening AFV ciphertexts with signed key features and modular ciphertext attributes
refs: [definition:WE_CircuitSAT, theorem:AdvancedEncryption.WE.IPE.weighted_attribute_factorization, theorem:AdvancedEncryption.WE.IPE.signed_binary_feature_square_bound]
tags: [witness-encryption, predicate-encryption, lwe, compiler]
---

The dyadic AFV table of [PR 97](https://github.com/MachinaIO/SigabaPark/pull/97) transmits a gadget block per predicate coordinate per ciphertext. The attribute in that block can be any element of Z/q. Large attribute coefficients multiply the noiseless term G^T s. Only the *key* coefficients multiply ciphertext errors and blinding matrices. This asymmetry lets us move algebraically expensive coefficients to the ciphertext side at compile time. On the two fixed table profiles of PR 97 the number of transmitted blocks falls from 1076 to 672 and from 831 to 608. This does not depend on deleting any table entries.

### Score and compiler

Use the split and the rankable key/ciphertext domains of [PR 93](https://github.com/MachinaIO/SigabaPark/pull/93). Keep the original rankers even when changing the CNF to an equivalent formula. For every old witness its restriction is still addressable; any extra address pair is checked against the complete new formula. Preprocess the residual by up to three rounds of clause strengthening and deletion. For a strengthening D ⊂ C, unit propagation in the current formula under the negation of D must produce a conflict. For a deletion of C, the check uses the remaining clauses under the negation of C. Strengthenings within a batch are justified by the original formula of that batch; deletions are replayed sequentially. Both operations preserve all assignments. The listing includes a second unit-propagation checker using incidence lists to replay the traces independently.

Use the minimum star cover from [PR 91](https://github.com/MachinaIO/SigabaPark/pull/91), which partitions the bipartite cross-clause edges. In the OR version each star contributes the product of the two indicators that at least one local subclause fails on the respective side. In the sum version each factor counts failed local subclauses at that endpoint. The product then counts failed edges of the star, so summing gives the number of failed cross clauses. Both scores vanish precisely when every cross clause passes. A local validity guard on each side is retained.

For a public anchor assignment, let the Boolean variables denote flips relative to that anchor. Express a failed subclause as a multilinear product of variable or complemented-variable literals. OR of failures is one minus the product of their complements. Work modulo q=2^512, reducing X_i²=X_i. On locally valid assignments every local failed-clause indicator is zero. Its leading monomial has coefficient ±1, so replace that monomial in a larger product by the signed combination of proper submonomials. This decreases the degree at every rewrite. The listing uses local clauses of width at most four; bounds on polynomial expansion trigger an independent opaque symbol for a feature that exceeds budget. Interpreting the symbol as the original feature makes every accepted identity valid. Different opaque symbols may represent correlated functions, which can lose compression.

Let x,y be the original column vectors of left and right star features on locally valid assignments. First find original left features x' and A with x=A x'. Keep unit pivots ±1 at this step and keep uneliminated nonunit rows as features. Form g=A^T y. Express its entries as modular polynomials on the right and find T and a subset y' of g with g=T y'. Odd unit pivots are allowed here since all coefficients of T move to the ciphertext side. The new attributes are T^T x' and the signed centered representatives of y' are the new key coefficients. The first accompanying Lean proof gives the score identity in any commutative ring. Each eliminated row carries its coefficients on retained original rows, and the compiler independently multiplies out these certificates. No field-rank assumption over a composite modulus is needed.

Use two guard coordinates, carrying (left-invalid,1) and (1,right-invalid). On an invalid side set its main vector to zero. Every pair then has canonical modular score z equal either to the original nonnegative cross score or to 1 or 2. In particular a rejected score is nonzero and bounded by max(2,number of residual clauses), even if some ciphertext coefficients are close to q. Do not use the absolute size of an unrestricted modular lift of each individual attribute as a bound on z.

### Security and noise accounting

In the real encryption equation ci=(Ai+wi G)^T s+Ri^T x_noise, the added gadget term cancels for every score-zero pair. In the selective hybrid, programming Ai=A Ri-wi* G changes the uniform column hash by a public translation independent of the blinding coins. For a rejecting signed key v, the shear is R=sum_i v_i Ri and the gadget multiplier is the canonical score z. The same short-basis proof for possibly even z applies. The base component of its Gram–Schmidt bound charges gcd(z,q) <= max(2,number of clauses). The spectrum and error estimates must instead charge the actual squared norm bound V of the signed coefficient vector.

For a signed combination of binary labels, each output coordinate is bounded in absolute value by the larger of its positive and negative coefficient masses. Squaring and summing is the second accompanying Lean theorem. For the sum encoding each old feature is itself a sum of at most the corresponding star degree of binary indicators, so the implementation can charge that multiplicity before taking the masses; no independence of the indicators is assumed. For a locally invalid key its main vector is zero and its two guards have squared norm two. For a valid right label exactly one guard is one. The two-width calculation of PR 97 replaces p by V in the mask and attribute-rounding squared error and the scalar variance used for the simulator's net bound. At a fixed input at most 2^128 distinct physical right labels occur, including any invalid label, since all of them are deterministic functions of at most 128 bits. Thus the logarithm of the net union count is at most 128. In the hash switch the number of matrix columns remains p' d, where p' is the transmitted dimension. The quotient operation and the rest of the LWE parameters are unchanged.

### Results

The first listing uses three public anchors and both OR and sum features. The following rows use sum features at the all-ones anchor except seed 1204, which uses the sampled anchor. Each strengthened/deleted trace was independently replayed. The old dimension includes the old local guard convention, and every new dimension includes both new guards.

| Control | Old dimension | Remaining CNF clauses | New dimension | V |
|---|---:|---:|---:|---:|
| Seed 851, 300 planted clauses | 1076 | 1644 | 672 | 32193 |
| Seed 854, 540 planted clauses | 831 | 2465 | 608 | 75407 |
| Seed 1202, 560 uniform clauses, refuted in PR 93 | 672 | 2383 | 495 | 79558 |
| Seed 1204, 560 uniform clauses | 911 | 2512 | 656 | 101969 |

At the original PR 97 K,C, both costed rows still choose ordinary-LWE dimension 131072, q=2^512, m=581714, d=262144, and 292606814 bits per key. The increased coefficient norms raise the attribute rounding widths to 291 and 292 bits respectively. The integer sweep includes these changes.

| Control | K | C | Bits per ciphertext | Whole table bits per WE bit | PiB | Reduction from PR 97 |
|---|---:|---:|---:|---:|---:|---:|
| 851 | 209012224 | 458752 | 51491709630 | 84780325727876096 | 9.413 | 14.07% |
| 854 | 8965806142 | 79437951 | 46768923326 | 6338683409645796614 | 703.735 | 16.87% |

Ciphertexts alone shrink by 37.01% and 25.73%. These are static wire counts excluding framing and preprocessing. On these particular planted controls the public decision paths documented in PRs 93 and 97 can bypass the encrypted table. The NO control and the fourth row test dimension reduction without relying on planted witnesses. No lower bound on the difficulty of deciding these inputs is asserted. Separate setup/attribute gadget radices were also swept at the old dimensions (setup target lengths 1–15, attribute target lengths 1–32): both optima retained the original equal 256-bit radix exponents. The reported improvement comes from the predicate compiler.

The two formal statements cover algebraic score preservation and the coefficient norm. Full quantum security, preprocessing clocks and the WE Submission remain open. A bounded compiler can fall back to the original representation whenever symbolic work or the wire-size estimate exceeds budget.

### Packing filtered domains with a public rank directory

The previous comparison fixes table counts to isolate the attribute optimization. A second compiler changes the counts. For each side retain only addresses satisfying a public set of necessary conditions for a *global* witness. This can use more local clauses than the crypto predicate: removing an entire address when emitting the table incurs no extra attribute coordinate. Keep every side-local clause of both the initial and simplified formulas, as well as earlier checked strengthened clauses that are side-local. Derive further necessary clauses as follows.

* Treat a mixed clause z or D with one opposite-side literal as a guarded demand for z when D fails. Follow the unguarded opposite-side binary implication graph. A pair of incompatible demands implies the union of their guards. A clause with up to three opposite literals also yields a side-only resolvent when demands force every opposite literal false. The listing caps the guard size at four and uses at most twelve requests per literal in the latter search.
* Use bounded directional resolution in three opposite-variable orders. Generate nontautological resolvents of length up to four, considering at most 48 parents per sign per variable. Discarding skipped parents/resolvents weakens the filter safely. Replay each generated resolution from its two parents and check retained guarded consequences by unit propagation. Remove subsumed side clauses. The bounded-inference approach is related to [Dechter and Rish](https://ijcai.org/proceedings/1997/187). The earlier strengthening step uses [clause vivification](https://doi.org/10.1016/j.artint.2019.103197).

Enc enumerates each public base domain in its original order. It writes a bit marking every retained address and emits dense crypto slots only at ones. Store a prefix count for every 512-bit block plus a final count. An original address i maps to the stored count for its block plus the number of earlier ones in the block. For a base domain of A addresses the bit budget used here is A+(ceil(A/512)+1)·ceil(log2(A+1)). A zero mark terminates that lookup. Every genuine witness has both marks set because every new clause is entailed by the original residual. The directory is a public deterministic function of the statement, independent of message and encryption coins. Invalid rows expose no key or encryption. Consequently the two guard coordinates can be dropped for this packed variant. The compiler also uses the stronger local equations when factoring the remaining valid features.

For counting, use component-cached exact #SAT on the side filters, including the factor of two for each free variable lost during restriction. The PR 93 rankers cover all locally valid assignments so the resulting counts are exact for those domains. For the more selective coupled ranker of PR 97, intersect the filter with its actual domain: at each surviving leaf condition on fixed side bits, conjoin its incidence forest, count the free solutions, and sum disjoint leaves. An encoder can always build the directory by streaming its actual base domain instead of completing the counting search. The clock must charge the chosen procedure. The measured counts use neither sampling nor an independence estimate.

| Control | Base domain | New p | Left C | Right K | Total PiB per WE bit including directory |
|---|---|---:|---:|---:|---:|
| 851 | PR 93 comparison row | 670 | 458752 | 155362546 | 7.662 |
| 854 | PR 93 depth 17 | 606 | 17789381 | 514308410 | 108.775 |
| 854 | PR 97 depth 9 | 606 | 10427839 | 280736999 | 63.088 |
| 854 | PR 97 depth 17 | 606 | 716405 | 8828271 | 3.994 |
| 1202 | PR 97 depth 17 | 493 | 56735 | 12722771 | 0.652 |
| 1204 | PR 97 depth 17 | 654 | 1092860 | 20818329 | 6.778 |

For the four controls in seed order the squared key norm bounds V are 32192, 75406, 79557 and 156996 at the all-ones anchor. Use the existing budget listing with the new p,V,K,C and add both directory bounds. Example: the seed-854 depth-17 coupled base has 8749398 and 123070763 addresses. Its two directories take 138720419 bits. Including the dense slots gives 35979026961487163 bits. Before filtering, the PR 97 two-width parameter sweep for that same base gave 586937534550603934 bits, or 65.163 PiB. The comparison is within the same public input and the same base ranker. Framing and computation are excluded as above.

**Public decision comparison.** A 65536-node public DPLL budget on the original formulas settles all four: seeds 851 and 854 are YES (58 and 4818 nodes) and 1202 and 1204 are NO (3753 and 10001 nodes). The independent PR 93 refutation checker also replayed the 10001-node proof for 1204. In particular an actual dispatcher using that inexpensive successful public path would emit none of the large tables in the table above. The results measure conditional encryption/compiler costs and do not demonstrate superiority over public decision or a reduced worst-case bound. In the 854 coupled depth-nine trees no witness appeared during construction; at depth seventeen both trees already find witnesses. Matching the depth-nine DPLL node cap alone would not account for the additional work of this compiler.


### Reproduction

Extract the Python listings from [PR 93 at its tested revision](https://github.com/MachinaIO/SigabaPark/blob/121e230357e9154fd838a3bbd5fc74dc9a06dd3b/dag/Notes/pq-we-latent-unit-profiles.md) and [PR 91 at its tested revision](https://github.com/MachinaIO/SigabaPark/blob/29b7f29db2ea0554e5ea76db6e3bdb4def2b50de/dag/Notes/pq-we-block-dominance.md) as latent.py and profiles.py. Run the first listing with those two paths, in that order. It checks 48,960 scores against the original CNFs over all assignments of 192 small formulas before compiling the four 128-input controls. The second listing runs the complete integer budget enumeration. The last listing runs with Sage/SymPy and takes the kernel/coset sampler from [PR 96](https://github.com/MachinaIO/SigabaPark/blob/9cc63482575bafbec9d17315f1f570f79ebc9b10/dag/Notes/pq-we-dyadic-afv.md) as its sole argument; it checks signed real keys, nonbinary attributes and a rejecting score of two.

~~~python
from collections import Counter
from random import Random
from math import log2
import sys,runpy
Q=1<<512

def addto(a,b,f):
    for k,v in b.items():
        w=(a.get(k,0)+v*f)%Q
        if w:a[k]=w
        else:a.pop(k,None)

def times(a,b,cap=256):
    if len(a)*len(b)>cap*8:raise OverflowError
    c={}
    for i,u in a.items():
        for j,v in b.items():
            w=(c.get(i|j,0)+u*v)%Q
            if w:c[i|j]=w
            else:c.pop(i|j,None)
    if len(c)>cap:raise OverflowError
    return c

def indicator(c,anchor):
    # Variables denote deviations from a public anchor assignment.
    z={0:1}
    for a in c:
        b=1<<(abs(a)-1)
        z=times(z,{b:1} if bool(anchor&b)==(a>0) else {0:1,b:-1})
    return z

def polynomial(clauses,anchor,mode):
    if mode=='one':return {0:1}
    if mode=='sum':
        z={}
        for c in clauses:addto(z,indicator(c,anchor),1)
        return z
    z={0:1}
    for c in clauses:
        a={0:1};addto(a,indicator(c,anchor),-1);z=times(z,a)
    o={0:1};addto(o,z,-1);return o

def basis(polys,small=False):
    # Retain original features as keys. Only eliminate using certified relations.
    pivot={};out={};kept=[]
    for i in sorted(range(len(polys)),key=lambda i:(len(polys[i]),i)):
        row=dict(polys[i]);comb={}
        # Pivot insertion order is triangular. Later rows have zero at every older pivot.
        for k,(pr,pc) in pivot.items():
            v=row.get(k,0)
            if v:addto(row,pr,-v);addto(comb,pc,v)
        if not row:out[i]=comb;continue
        kept.append(i);out[i]={i:1}
        unit=[k for k,a in row.items() if (a in (1,Q-1) if small else a&1)]
        if unit:
            k=max(unit,key=lambda j:(j.bit_count(),j))
            u=pow(row[k],-1,Q); pc={i:1};addto(pc,comb,-1)
            pivot[k]=({j:a*u%Q for j,a in row.items()},{j:a*u%Q for j,a in pc.items()})
    for i,p in enumerate(polys):
        verify={}
        for j,a in out[i].items():addto(verify,polys[j],a)
        assert p==verify
    return kept,out

from itertools import combinations
from functools import lru_cache

def normalizer(clauses,anchor,n):
    rules={}
    for c in sorted(clauses,key=lambda c:(len(c),c)):
        if not 1<=len(c)<=4:continue
        mask=sum(1<<(abs(a)-1) for a in c)
        if mask in rules:continue
        poly=indicator(c,anchor);u=poly.pop(mask)
        rules[mask]={j:-a*pow(u,-1,Q)%Q for j,a in poly.items()}
    @lru_cache(maxsize=32000)
    def normal(mask):
        bits=[1<<i for i in range(n) if mask>>i&1]
        for k in range(1,min(4,len(bits))+1):
            for subset in combinations(bits,k):
                key=sum(subset)
                if key not in rules:continue
                z={}
                for j,a in rules[key].items():
                    addto(z,normal((mask^key)|j),a)
                    if len(z)>256:raise OverflowError
                return z
        return {mask:1}
    def reduce(poly):
        z={}
        for k,a in poly.items():
            addto(z,normal(k),a)
            if len(z)>256:raise OverflowError
        return z
    return reduce

class Implications:
    def __init__(self,rows):
        self.rows=tuple(rows);self.occ=Counter()
        self.levels=[0]*(2+max(map(len,rows),default=0))
        for i,c in enumerate(rows):
            self.levels[len(c)]|=1<<i
            for a in c:self.occ[a]|=1<<i
    def reason(self,active,i,order,include=False):
        allowed=active if include else active&~(1<<i)
        levels=tuple(x&allowed for x in self.levels)
        fixed=set()
        def assign(a):
            nonlocal levels
            fixed.add(a)
            kill=self.occ[a]|self.occ[-a];opp=self.occ[-a]
            levels=tuple((l&~kill)|(levels[j+1]&opp if j+1<len(levels) else 0)
                         for j,l in enumerate(levels))
        prefix=[]
        for a in order+(0,):
            while levels[1] and not levels[0]:
                j=(levels[1]&-levels[1]).bit_length()-1
                u,=(l for l in self.rows[j] if -l not in fixed)
                assign(u)
            if levels[0]:return tuple(prefix)
            if a==0:return None
            if a in fixed:return tuple(prefix+[a])
            if -a not in fixed:prefix.append(a);assign(-a)
        raise AssertionError

def prune(rows,rounds):
    F=sorted({tuple(sorted(set(c))) for c in rows if not any(-a in c for a in c)},key=lambda c:(len(c),c))
    trace=[]
    for _ in range(rounds):
        I=Implications(F);act=(1<<len(F))-1
        for i in reversed(range(len(F))):
            c=F[i];o=tuple(sorted(c,key=lambda a:(-I.occ[a].bit_count(),a)))
            res=I.reason(act,i,o)
            if res is None:continue
            act^=1<<i
            trace.append((c,tuple(sorted(res))))
        new=sorted({c for i,c in enumerate(F) if act>>i&1},key=lambda c:(len(c),c))
        if new==F:break
        F=new
    return F,trace


def tighten(rows):
    F=sorted({tuple(sorted(set(c))) for c in rows if not any(-a in c for a in c)},key=lambda c:(len(c),c))
    stages=[]
    for turn in range(3):
        I=Implications(F);active=(1<<len(F))-1;out=[];changes=[]
        for i,c in enumerate(F):
            best=c
            orders=[tuple(sorted(c,key=lambda a:(-I.occ[a].bit_count(),a))),
                    tuple(sorted(c,key=lambda a:(I.occ[a].bit_count(),-a)))]
            for order in orders:
                proof=I.reason(active,i,order,include=True)
                if proof is not None and len(proof)<len(best):best=tuple(sorted(proof))
            if best!=c:changes.append((c,best))
            out.append(best)
        G,trace=prune(out,1)
        stages.append((changes,trace))
        if G==F:break
        F=G
    return F,stages

def side_polys(cover,loc,anchor,n,side,style):
    reduce=normalizer(loc[side],anchor,n)
    polys=[]
    for i,pair in enumerate(cover):
        try:polys.append(reduce(polynomial(pair[side],anchor,style)))
        except OverflowError:polys.append({1<<(n+i):1})
    return polys

def pack(cover,loc,anchor,n,style):
    L,A=basis(side_polys(cover,loc,anchor,n,0,style),small=True)
    R=side_polys(cover,loc,anchor,n,1,style)
    terms={j:{} for j in L};pos=Counter();neg=Counter()
    for i,row in A.items():
        for j,coeff in row.items():
            addto(terms[j],R[i],coeff)
            z=coeff if coeff<=Q//2 else coeff-Q
            z*=len(cover[i][1]) if style=="sum" else 1
            if z>0:pos[j]+=z
            else:neg[j]-=z
    J,T=basis([terms[j] for j in L])
    V=1+sum(max(pos[L[k]],neg[L[k]])**2 for k in J)
    return L,A,J,T,V

def apply_map(certificate,cover,loc,m,x,side,style):
    L,A,J,T,_=certificate
    bad=int(not m['satisfies'](loc[side],x))
    if bad:return [0]*len(J)+[1,1]
    combine=any if style=='or' else sum
    orig=[int(combine(not m['satisfies']([c],x) for c in row[side])) for row in cover]
    if side==0:
        w=Counter()
        for k,j in enumerate(L):
            if orig[j]:addto(w,T[k],orig[j])
        return [w[j] for j in J]+[0,1]
    g=Counter()
    for i in range(len(cover)):
        if orig[i]:addto(g,A[i],orig[i])
    return [(g[L[j]] if g[L[j]]<=Q//2 else g[L[j]]-Q) for j in J]+[1,0]

def replay(initial,stages):
    # A second RUP checker uses clause occurrences and counts falsified literals.
    class Check:
        def __init__(self,rows):
            self.rows=list(rows);self.idx={c:i for i,c in enumerate(self.rows)}
            self.live=set(range(len(self.rows)));self.at={};self.units=[]
            for i,c in enumerate(self.rows):
                if len(c)<=1:self.units.append(i)
                for a in c:self.at.setdefault(a,[]).append(i)
        def conflict(self,clause):
            todo=[-a for a in clause];fixed=set();count=Counter()
            for i in self.units:
                if i not in self.live:continue
                if not self.rows[i]:return True
                todo.append(self.rows[i][0])
            while todo:
                a=todo.pop()
                if -a in fixed:return True
                if a in fixed:continue
                fixed.add(a)
                for i in self.at.get(-a,()):
                    if i not in self.live:continue
                    count[i]+=1;c=self.rows[i]
                    if count[i]==len(c):return True
                    if count[i]+1==len(c):
                        todo.append(next(z for z in c if -z not in fixed))
            return False
    db={tuple(sorted(set(c))) for c in initial if not any(-a in c for a in c)}
    for changed,deleted in stages:
        check=Check(db);new=set(db)
        for old,short in changed:
            assert old in db and set(short)<set(old) and check.conflict(short)
        for old,short in changed:new.discard(old)
        new.update(short for old,short in changed)
        check=Check(new)
        for c,_ in deleted:
            check.live.remove(check.idx[c])
            assert check.conflict(c)
            new.remove(c)
        db=new
    return db

def test_all(m):
    gen=Random(511);tested=0
    for n in range(2,10):
        for i in range(24):
            V=list(range(1,n+1));left={v for v in V if gen.randrange(2)}
            F=[tuple(v*gen.choice((-1,1)) for v in gen.sample(V,gen.randint(1,min(4,n))))
               for _ in range(gen.randint(1,3*n+2))]
            red,steps=tighten(F)
            assert replay(F,steps)==set(red)
            loc,_,cover=m['compile_cnf'](n,red,left)
            for style in ('or','sum'):
                cert=pack(cover,loc,gen.getrandbits(n),n,style)
                for x in range(1<<n):
                    w=apply_map(cert,cover,loc,m,x,0,style)
                    v=apply_map(cert,cover,loc,m,x,1,style)
                    assert sum(a*a for a in v)<=max(2,cert[-1])
                    score=sum(a*b for a,b in zip(v,w))%Q
                    assert (score==0)==m['satisfies'](F,x)
                    assert score<=max(2,len(red))
                    tested+=1
    print('exhaustive scores',tested,flush=True)

def bench(path93,path91):
    sys.argv=[path93,path91];ds=runpy.run_path(path93); m=ds['m'];test_all(m)
    for seed,num in [(851,300),(854,540),(1202,560),(1204,560)]:
        F=(m['planted'](128,num,seed)[1] if seed<1000 else ds['generate'](128,num,seed))
        r,*_=m['project'](F,128,8,0); rr=r
        for rr,_ in ds['massage'](r,rounds=6 if num==300 else 4):pass
        rows,_,vs=m['shrink'](rr,set(),128)
        if num==300:left=set(range(1,1+max(0,round((len(vs)-log2(max(1,len(rr)/2)))/2))))
        else:left=ds['fit'](rows,40 if num==540 else len(vs)//2-3)
        initial=rows; rows,stages=tighten(rows);assert replay(initial,stages)==set(rows);trace=[z for x,y in stages for z in x+y]
        loc,edges,cover=m['compile_cnf'](len(vs),rows,left)
        g=Random(146);result=[]
        for a in [0,(1<<len(vs))-1,g.getrandbits(len(vs))]:
            for style in ("or","sum"):
                L,A,J,T,V=pack(cover,loc,a,len(vs),style)
                result.append((style,len(J)+2,max(2,V)))
        print(seed,len(rows),len(trace),len(cover),result,flush=True)
if __name__=='__main__':bench(sys.argv[1],sys.argv[2])

~~~

~~~python
from math import isqrt
from itertools import product

def ceildiv(x,y):return (x+y-1)//y
def ceilroot(x):
    r=isqrt(x)
    return r+(r*r<x)
def calc(p,K,C,t,r,V,score_cap):
    n=1<<17;e=512;d=n*ceildiv(e,r);M=1<<21
    slack=e+(e-1).bit_length()+2*(384+(p*d).bit_length())
    setup_slack=(e-1).bit_length()+2*(384+d.bit_length())
    a=max(n+setup_slack,ceildiv(n*e+setup_slack,t));m=a+d
    t_enc=ceildiv(n*e+slack,m)
    if m<n+slack or t_enc>e:return None
    if m+1>M:return None
    lg=lambda x:(x-1).bit_length()
    s=r+9+max(t+ceildiv(lg(a+d+400),2),
              t_enc+ceildiv(lg(V*(m+d+128+400)),2))
    if 16*score_cap>(1<<s):return None
    L=m+d; J=m-n; sg=r+6
    Y2=256*(1<<(2*s))*L; G2=256*(1<<(2*sg))*L
    # Condition on the sampled key. Three errors: base noise, mask noise, wire rounding.
    # For each, enforce 2 exp(-2 threshold^2 / sum widths^2) <= 2^-159
    # using exponent >=160 and e>=2 as the natural exponential base.
    q=1<<e
    lim=q//16
    if 2*lim**2 < 160*32**2*(1+Y2):return None
    if 2*lim**2 < 160*(2<<t_enc)**2*256*m*V*G2:return None
    half_log=lambda x:ceildiv(lg(x),2)
    ha=min(e,half_log(81920*Y2)); hg=min(e,half_log(20480*V*G2))
    def best_slot(length,exponent):
        def slot(b):return length*(b+1)+(32*(1<<exponent)*ceilroot(length*L))//(1<<b)
        return min((slot(b),b) for b in range(exponent+2,exponent+12))
    ka,ba=best_slot(J,s);kg,bg=best_slot(d,sg)
    key=ka+kg;ct=6+J*ha+p*d*hg
    return (key*K+ct*C,r,t,t_enc,s,sg,ba,bg,ha,hg,m,d,key,ct)


if __name__=='__main__':
    for name,p,V,K,C,cap in [('851-or',677,2904,209012224,458752,1644),
                              ('851-sum',672,32193,209012224,458752,1644),
                              ('854-or',617,4099,8965806142,79437951,2465),
                              ('854-sum',608,75407,8965806142,79437951,2465)]:
        rows=(calc(p,K,C,t,ceildiv(512,k),V,cap) for k in range(1,65) for t in range(1,513))
        print(name,min(a for a in rows if a))

~~~

~~~python
import runpy,sys
from random import Random
from sympy import Matrix,eye,zeros,diag

def weighted_check(path):
    K=runpy.run_path(path); basis_for=K['right_basis']; klein=K['klein']
    rng=Random(532);e=64;q=1<<e;r=8;n=1;d=8;a=4;m=a+d;p=3
    G=K['gadget'](n,e,r)
    def uniform(h,w):return Matrix(h,w,lambda i,j:rng.randrange(q))
    def wide(h,w):return Matrix(h,w,lambda i,j:rng.randrange(4)-rng.randrange(4))
    def cbd():return rng.getrandbits(16).bit_count()-rng.getrandbits(16).bit_count()
    A0=uniform(n,a);S=wide(a,d);A=A0.row_join((G-A0*S)%q)
    Ai=[uniform(n,d) for _ in range(p)];u=uniform(n,1);C=-Ai[0]-Ai[1]
    sa=1<<20; sg=1<<14
    scale=diag(eye(m),(sa//sg)*eye(d))
    def sample(basis,point):
        z=klein(scale*basis,scale*point,sa,rng)
        assert all(int(x)%(sa//sg)==0 for x in z[m:,:])
        return z[:m,:].col_join(z[m:,:]/(sa//sg))
    B,f=basis_for(A0.row_join(C),e,r,-1,(-S).col_join(zeros(d,d)),u)
    order=list(range(a))+list(range(a+d,a+2*d))+list(range(a,a+d))
    key=sample(B[order,:],f[order,:])
    assert all(int(x)%q==0 for x in A.row_join(C)*key-u)
    pivot=next(i for i in range(m) if int(A[0,i])%2)
    keep=[i for i in range(m) if i!=pivot]
    for msg in (0,1):
        s=Matrix([cbd()]);x=Matrix([cbd() for _ in range(m)])
        s0=Matrix([(-int(x[pivot])*pow(int(A[0,pivot]),-1,q))%q])
        def quant(z,h):
            step=q>>h;lo,rem=divmod(int(z)%q,step)
            return (step*(lo+(rng.randrange(step)<rem)))%q
        base=(A.T*s0+x)[keep,:].applyfunc(lambda z:quant(z,60))
        blocks=[(M.T*s0+wi*G.T*s+wide(m,d).T*x).applyfunc(lambda z:quant(z,52))
                for wi,M in zip((2,-2,0),Ai)]
        label=quant(u.dot(s0)+cbd()+msg*(q//2),6)
        residual=int(label-key[keep+list(range(m,m+d)),:].dot(base.col_join(-blocks[0]-blocks[1])))%q
        assert int(q//4<=residual<3*q//4)==msg
    Rs=[wide(m,d) for _ in range(p)]
    sim=[A*R-b*G for R,b in zip(Rs,(-4,2,0))]
    B,f=basis_for(A,e,r,2,-Rs[0]-Rs[1],u)
    sk=sample(B,f)
    assert all(int(x)%q==0 for x in A.row_join(-sim[0]-sim[1])*sk-u)
    print('negative key coefficients, signed attributes, both bits and simulated score two passed')
if __name__=='__main__':weighted_check(sys.argv[1])

~~~

For packed domains, save the first listing as compact.py and the following as filter.py. Run it with the three paths latent.py, profiles.py and compact.py. It checks the domain filter, exact counts and directory lookup on 140 small formulas (3981 retained pairs), then replays the large filter proofs.

~~~python
from functools import lru_cache
from collections import Counter
import runpy,sys
from math import log2,prod
def trim(cs,side):
    calls=0
    def canonical(cs):return tuple(sorted(set(tuple(sorted(c)) for c in cs)))
    def scope(cs):return {abs(a) for c in cs for a in c}
    def restrict(cs,a):return canonical(tuple(v for v in c if v!=-a) for c in cs if a not in c)
    @lru_cache(None)
    def count(cs):
        nonlocal calls
        calls+=1
        if () in cs:return 0
        if not cs:return 1
        V=scope(cs)
        def sub(a):
            reduced=restrict(cs,a);lost=V-{abs(a)}-scope(reduced)
            return (1<<len(lost))*count(reduced)
        unit=next((c[0] for c in cs if len(c)==1),None)
        if unit is not None:return sub(unit)
        par={v:v for v in V}
        def root(v):
            while par[v]!=v:par[v]=par[par[v]];v=par[v]
            return v
        for c in cs:
            p=root(abs(c[0]))
            for l in c[1:]:par[root(abs(l))]=p
        groups={}
        for c in cs:groups.setdefault(root(abs(c[0])),[]).append(c)
        if len(groups)>1:return prod(count(tuple(g)) for g in groups.values())
        freq=Counter(abs(a) for c in cs for a in c)
        v=max(V,key=lambda v:(freq[v],-v))
        return sub(v)+sub(-v)
    cs=canonical(cs);result=(1<<len(set(side)-scope(cs)))*count(cs)
    count.cache_clear()
    return result,calls
from itertools import combinations
def bucket_filter(rows,side,width=4,proof=None):
    known=set(map(frozenset,rows))
    # Three public elimination orders. Long mixed clauses may be dropped; every
    # emitted clause is still an implicate of the original CNF.
    loc={frozenset(c) for c in rows if all(abs(a) in side for a in c)}
    hidden={abs(a) for c in rows for a in c if abs(a) not in side}
    for mode in range(3):
        bag={frozenset(c) for c in rows if len(c)<=width}
        live=set(hidden)
        while live:
            freq=Counter(a for c in bag for a in c)
            if mode==0:v=min(live,key=lambda x:(freq[x]*freq[-x],x))
            elif mode==1:v=min(live)
            else:v=max(live)
            live.remove(v)
            pos=[c for c in bag if v in c];neg=[c for c in bag if -v in c]
            bag.difference_update(pos,neg)
            def shortlist(cs):
                return sorted(cs,key=lambda c:(len(c),sum(abs(a) in live for a in c),tuple(sorted(c))))[:48]
            made=set()
            for a in shortlist(pos):
                for b in shortlist(neg):
                    u=(a|b)-{v,-v}
                    if len(u)<=width and not any(-i in u for i in u):
                        made.add(u)
                        if proof is not None and u not in known:
                            proof.append((a,b,v,u));known.add(u)
            bag.update(made)
        loc.update(bag)
    return loc

def projected_filter(rows,side,maxlen=4,cc=None):
    side=set(side); local=set(); graph={}; requests={}
    for c in rows:
        a=frozenset(z for z in c if abs(z) in side);b=[z for z in c if abs(z) not in side]
        if not b:local.add(a)
        elif len(b)==1 and len(a)<=maxlen:requests.setdefault(b[0],set()).add(a)
        elif len(b)==2 and not a:
            x,y=b;graph.setdefault(-x,set()).add(y);graph.setdefault(-y,set()).add(x)
    entailed=set();causes={}
    for l,A in requests.items():
        seen={l};stack=[l]
        while stack:
            for b in graph.get(stack.pop(),set())-seen:seen.add(b);stack.append(b)
        for h in seen:
            causes.setdefault(h,set()).update(A)
            for a in A:
                for b in requests.get(-h,()):
                    merged=a|b
                    if len(merged)<=maxlen and not any(-i in merged for i in merged):
                        entailed.add(merged)
    # A mixed clause with at most three opposite literals closes a contradiction
    # if each of them is forced false by an active guarded request.
    for c in rows:
        a=frozenset(z for z in c if abs(z) in side)
        opp=[z for z in c if abs(z) not in side]
        if not 2<=len(opp)<=3 or len(a)>maxlen:continue
        guards=[sorted(causes.get(-b,()),key=lambda D:(len(D),tuple(sorted(D))))[:12] for b in opp]
        partial={a}
        for choices in guards:
            partial={d|g for d in partial for g in choices if len(d|g)<=maxlen and
                     not any(-j in d for j in g)}
        entailed.update(partial)
    proof=[];bucket=bucket_filter(rows,side,maxlen,proof);keep=set()
    for c in sorted(entailed|local|bucket,key=lambda c:(len(c),tuple(sorted(c)))):
        if not any(frozenset(z) in keep for k in range(min(len(c),maxlen)+1) for z in combinations(c,k)):
            keep.add(c)
    if cc is not None:
        valid=set(map(frozenset,rows))
        for a,b,v,u in proof:
            assert a in valid and b in valid and v in a and -v in b and (a|b)-{v,-v}==u
            valid.add(u)
        check=cc['Implications']([tuple(sorted(c)) for c in valid])
        active=(1<<len(check.rows))-1
        for c in keep-valid:
            assert check.reason(active,0,tuple(sorted(c)),include=True) is not None
    return [tuple(sorted(c)) for c in keep]

def filter_tests(m,cc):
    from random import Random
    g=Random(621);pairs=0
    for _ in range(140):
        n=g.randint(2,9);V=set(range(1,n+1));left={i for i in V if g.randrange(2)}
        F=[tuple(v*g.choice((-1,1)) for v in g.sample(sorted(V),g.randint(0,min(4,n)))) for _ in range(g.randint(0,16))]
        red,trace=cc['tighten'](F)
        assert cc['replay'](F,trace)==set(red)
        learned={tuple(sorted(c)) for c in F}|set(red)
        for changed,_ in trace:learned.update(c for _,c in changed)
        filters=[projected_filter(learned,side,cc=cc) for side in (left,V-left)]
        kept=[];index=[]
        for side,clauses in zip((left,V-left),filters):
            ordered=[z for z in range(1<<n) if not (z&~sum(1<<(v-1) for v in side))]
            mask=[int(m['satisfies'](clauses,z)) for z in ordered]
            kept.append([z for z,b in zip(ordered,mask) if b])
            assert len(kept[-1])==trim(clauses,side)[0]
            idx={};prefix=[0]
            for j,b in enumerate(mask):
                if j and j%4==0:prefix.append(prefix[-1]+sum(mask[j-4:j]))
                if b:idx[ordered[j]]=prefix[j//4]+sum(mask[(j//4)*4:j])
            index.append(idx)
        loc,_,cover=m['compile_cnf'](n,red,left)
        cert=cc['pack'](cover,filters,0,n,'sum')
        lm=sum(1<<(v-1) for v in left)
        for x in range(1<<n):
            l=x&lm;r=x&~lm;yes=m['satisfies'](F,x)
            if l not in index[0] or r not in index[1]:assert not yes;continue
            assert kept[0][index[0][l]]==l and kept[1][index[1][r]]==r
            w=cc['apply_map'](cert,cover,filters,m,l,0,'sum')[:-2]
            v=cc['apply_map'](cert,cover,filters,m,r,1,'sum')[:-2]
            assert yes==(sum(a*b for a,b in zip(w,v))%cc['Q']==0)
            pairs+=1
    print('filtered pair checks',pairs,flush=True)

def bench(a,b,compiler):
    cc=runpy.run_path(compiler)
    sys.argv=[a,b];ns=runpy.run_path(a);m=ns['m'];filter_tests(m,cc)
    for seed,num in [(851,300),(854,540),(1202,560),(1204,560)]:
        F=(m['planted'](128,num,seed)[1] if seed<1000 else ns['generate'](128,num,seed))
        r,*_=m['project'](F,128,8,0);rr=r
        for rr,_ in ns['massage'](r,rounds=6 if num==300 else 4):pass
        rows,_,vs=m['shrink'](rr,set(),128)
        left=(set(range(1,1+max(0,round((len(vs)-log2(max(1,len(rr)/2)))/2)))) if num==300 else ns['fit'](rows,40 if num==540 else len(vs)//2-3))
        red,trace=cc['tighten'](rows)
        assert cc['replay'](rows,trace)==set(red)
        learned={tuple(sorted(c)) for c in rows}|set(red)
        for changed,deleted in trace:learned.update(c for _,c in changed)
        loc,_,cover=m['compile_cnf'](len(vs),red,left)
        domains=[]
        vals=[]
        for side in (left,set(range(1,len(vs)+1))-left):
            filters=projected_filter(learned,side,cc=cc)
            domains.append(filters)
            vals.append((len(filters),*trim(filters,side)))
        cert=cc['pack'](cover,domains,(1<<len(vs))-1,len(vs),'sum')
        print(seed,vals,'dimension',len(cert[2]),'norm',cert[-1]-1,flush=True)
if __name__=='__main__':bench(*sys.argv[1:])

~~~

The final listing additionally takes filter.py and the coupled tree listing from [PR 97](https://github.com/MachinaIO/SigabaPark/blob/7220172e0d6dd4ff34f718aed28e63b03688a9f8/dag/Notes/pq-we-coupled-domains-and-pivot-quotient.md), as the fourth and fifth paths. It checks 160 small intersections by direct rank enumeration.

~~~python
import runpy,sys
from math import log2
def intersection(tree,side,filters,trim):
    cache={};work=0;leaves=0
    def walk(tree):
        nonlocal work,leaves
        count,node=tree
        if not count:return 0
        if len(node)==3:return walk(node[1])+walk(node[2])
        fixed,vs,forest,_=node;leaves+=1
        residual=set(tuple(sorted(c)) for c in forest)
        for c in filters:
            if any(abs(a) not in vs and bool(fixed>>(abs(a)-1)&1)==(a>0) for a in c):continue
            u=tuple(a for a in c if abs(a) in vs)
            if not u:return 0
            residual.add(u)
        sig=(frozenset(vs),frozenset(residual))
        if sig not in cache:
            k,steps=trim(residual,vs);work+=steps;cache[sig]=k
        return cache[sig]
    return walk(tree),leaves,work
def check_intersections(ds,df,P,cc):
    from random import Random
    g=Random(615);m=ds['m']
    for _ in range(160):
        n=g.randint(2,9);side={v for v in range(1,n+1) if g.randrange(2)}
        F=[tuple(v*g.choice((-1,1)) for v in g.sample(range(1,n+1),g.randint(1,min(4,n))))
           for _ in range(g.randint(1,3*n))]
        filters=df['projected_filter'](F,side,cc=cc)
        T=P(F,side,g.randint(0,4),ds)
        expected=sum(m['satisfies'](filters,T.address(j,True)) for j in range(T.root[0]))
        assert intersection(T.root,side,filters,df['trim'])[0]==expected

def bench(a,b,c,f,h):
    sys.argv=[a,b];ds=runpy.run_path(a);m=ds['m'];cc=runpy.run_path(c);df=runpy.run_path(f);P=runpy.run_path(h)['Projection']
    check_intersections(ds,df,P,cc)
    for seed,num in [(854,540),(1202,560),(1204,560)]:
        F=(m['planted'](128,num,seed)[1] if seed==854 else ds['generate'](128,num,seed));r,*_=m['project'](F,128,8,0)
        for rr,_ in ds['massage'](r,rounds=4):pass
        rows,_,vs=m['shrink'](rr,set(),128);left=ds['fit'](rows,40 if seed==854 else len(vs)//2-3)
        red,trace=cc['tighten'](rows);learned={tuple(sorted(c)) for c in rows}|set(red)
        for changed,_ in trace:learned.update(c for _,c in changed)
        tables=[]
        for side in (left,set(range(1,len(vs)+1))-left):
            filters=df['projected_filter'](learned,side)
            res=[]
            for depth in (9,17):
                T=P(rows,side,depth,ds)
                res.append((T.root[0],*intersection(T.root,side,filters,df['trim']),T.models))
            tables.append(res)
        print(seed,tables,flush=True)
if __name__=='__main__':bench(*sys.argv[1:])

~~~
