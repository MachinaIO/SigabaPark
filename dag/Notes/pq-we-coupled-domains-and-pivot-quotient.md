---
title: Compressing split-witness tables by projected unit propagation and public syndrome cancellation
refs: [definition:WE_CircuitSAT, theorem:AdvancedEncryption.WE.IPE.pivot_quotient_residual]
tags: [witness-encryption, predicate-encryption, lwe, compiler]
---

The target is the one-bit circuit-SAT WE of this DAG. Two optimizations change different factors of the wire budget in [PR 96](https://github.com/MachinaIO/SigabaPark/pull/96): how many entries are needed, and how many coordinates each entry carries. The compiler takes a Boolean CNF residual with a witness-preserving restriction map as in [PR 93](https://github.com/MachinaIO/SigabaPark/pull/93). It keeps the original cross-clause zero-inner-product predicate, including the two local validity flags. The algebraic compression applies also without that compiler.

### Removing n coordinates from every key and ciphertext

Write an unrounded predicate ciphertext as (c0, c1, ..., cp, b), where the last coordinate carries the masked message. Let F_v=[A | sum_i v_i A_i], u be the public target, and F_v y=u modulo q the key invariant. The vector used in decryption is c=(c0, sum_i v_i ci). The residual is b-<c,y>. Select n pivot columns P of A forming a matrix A_P invertible modulo q=2^e. These pivots are shared by every v. In real setup A=[A0 | G-A0 S]; modulo two its column span contains the columns of G, which contains the n coordinate vectors. Ordinary elimination over F_2 therefore finds n independent columns. The resulting minor has odd determinant and is invertible modulo q. In a simulation with uniform A, use the rank-failure handling already charged in PR 96, or implement a full-width fallback with a public mode bit.

For each ciphertext solve A_P^T d=(c0)_P modulo q using the inverse prepared once. Replace c0 by c0-A^T d, ci by ci-A_i^T d and b by b-<d,u>. The selected base coordinates are zero. Serialize the remaining base entries in the common column order, all attribute entries, and the scalar. For each key drop the same coordinates of its base part, leaving its attribute part intact. Dec takes the inner product of the shortened key and combined ciphertext in their transmitted order. It needs neither the deleted entries nor A, A_i, d, the pivots, or a syndrome decoder. The public predicate labels/indices and ordinary table layout are still needed.

The attached Lean theorem proves the exact residual identity over any commutative ring. The effective subtraction from the combined vector is F_v^T d. This cancels exactly against the scalar adjustment for *every* v. Apply the short-coordinate rounding of PR 96 **after** this change. Its worst-case error bound still holds because the deleted terms contribute zero and deletion cannot increase the retained key norm. A distinguisher for the transformed classical data induces one for the full unrounded data by this deterministic public map, also under quantum postprocessing. That reduction uses the public matrices. If comparing to a game exposing only already-rounded data, use the earlier unrounded hybrid. The transform supplies no additional hardness premise.

A direct implementation can avoid a second set of matrix products. Put s0=s-d and generate the new base as A^T s0+x on the retained indices, and the new blocks as A_i^T s0+w_i G^T s+R_i^T x. With c0=A^T s+x, one can compute s0=-A_P^(-T) x_P directly. The scalar similarly uses u^T s0. The original s remains necessary in the attribute term. A bound for preprocessing the dense inverse and a full explicit machine clock still belong in a WE Submission. The key sampler still produces the original short vector internally.

At fixed PR 96 parameters n=131072, q=2^512, let k and h be the transmitted bit widths per key and ciphertext coordinate, and K,C the table counts. The exact saving, excluding framing, is n(kK+hC) bits for one WE message bit. On the 1076-coordinate profile (k,h)=(319,343) the table drops from 166786968291757568 to 158027131437305344 bits (18.517 to 17.545 PiB). On the 831-coordinate profile (386,409), it drops from 11945295824085201989 to 11487423147759121477 bits (3.83%). No public-matrix transmission charge is introduced by the change. These are serialization estimates. The combined scheme's reduction clock and quantum security remain open.

### Smaller fixed slots and a per-witness correctness budget

A second parameter sweep keeps the same certified ordinary-LWE row (n=2^17, M=2^21, e=512). It bounds the trapdoor spectral norm with high probability, encodes signed keys losslessly in fixed slots, and spends part of the WE correctness error on unbiased ciphertext rounding. This is an analytic variant; the preceding pivot identity is the part checked in Lean.

**Trapdoor width.** For independent centered entries U-V with magnitude below 2^t, a fixed pair of Euclidean unit vectors x,y and a fixed nonempty v give a scalar x^T(sum v_i R_i)y. The sum of squared summand range widths is at most 4·2^(2t) p, since sum(x_j² y_k²)=1. Apply [Hoeffding's inequality, Theorem 2](https://doi.org/10.1080/01621459.1963.10500830). For L=m+d, put T=4·2^t sqrt(p(L+p+400)). The scalar exceeds T in absolute value with probability at most 2 exp(-8(L+p+400)). A maximal 1/4-separated net of each unit sphere has at most 9^m and 9^d points respectively by the disjoint-ball volume bound. Approximating both unit vectors by net points loses at most half the operator norm. A union bound over the nets and all 2^p predicates thus gives ||sum v_i R_i|| <= 2T simultaneously, except with probability below 2^-400. The zero selector is automatic. The same bound covers the real a-by-d S with a single matrix by a separate application. Each hybrid charges its corresponding bad draw. In the key sampler check the computed basis widths, and abort if a width exceeds the cap. The algorithm need not enumerate a net or all selectors. For the table rows, sigma=2^s with s=r+9+t+ceil(log2(p(L+p+400))/2) covers 16 times the good Gram–Schmidt ceiling max(p,(1+2T)sqrt(2^(2r)+1)). This retains PR 96's one-dimensional sampler width condition and its completed-key norm Y <= 16 sigma sqrt(L).

**Decryption error.** For a fixed valid witness and its selected completed key, charge three tails. First, x'-x^T y_base is centered with squared range-width sum bounded by 32²(1+Y²). Second, conditional on x and this key, the mask error sum_i v_i x^T R_i y_attr is centered and has squared range-width sum at most (2·2^t)²·256 m p Y². Here the real encryption masks are fresh and independent of the key. For both errors use threshold q/16. Finally, independently round each *corrected* coordinate on a grid of spacing Delta=q/2^h. If the low remainder is z, choose the upper endpoint with probability z/Delta by comparing fresh fair bits to z; reduce the endpoint modulo q for transport. The centered modular error has a lift of range width at most Delta. Conditional on the original full ciphertext and key, the rounded decryption residual has extra squared range-width sum at most Delta²(1+pY²). Use threshold q/8. Whenever each tail is strictly within its threshold the total is strictly below q/4. The final listing requires the exponent 2 threshold² / sum(width²) to be at least 160 in each application. Each two-sided failure probability is then at most 2^-159, so the sum of the three errors leaves room below 2^-128 for basis and sampler failures. WE correctness is per fixed witness; simultaneous correctness of every pair would require a different budget. The security hybrid uses a public randomized output map with independent rounding coins. Account for the additional e-h fair bits per transmitted scalar in the clock.

**Fixed key slots.** Let J=L-n be the retained key length. Zig-zag encode signed y_j as 2y_j for y_j>=0 and -2y_j-1 otherwise. Rice-code each value with b low bits, followed or preceded consistently by its unary high quotient and terminator. Cauchy–Schwarz gives sum |y_j| <=16 sigma sqrt(J L). Pad every key to exactly J(b+1)+floor(32 sigma ceil(sqrt(J L))/2^b) bits. The decoder stops after J words. Rank lookup uses the same public slot size even when a particular key is unusually compressible. This bound is deterministic for every completed truncated key; it adds no probability of key loss.

The sweep runs all t in [1,512] and r=ceil(512/k) for k=1,...,64. Smaller costs may exist outside these choices. The helper checks m+1<=M and all three integer tail thresholds. Both winners have r=256, d=262144. They use the same K,C as the fixed PR 96 profiles, before any pruning:

| p | t | m | log2 sigma | low key bits b | ciphertext width h | bits per key slot | table bits per WE bit | saving from PR 96 |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 1076 | 94 | 976083 | 375 | 380 | 401 | 422996914 | 140455882421480448 | 15.79% |
| 831 | 91 | 999619 | 371 | 376 | 397 | 427464938 | 10730002534920127160 | 10.17% |

This changes both the retained vector lengths and their widths. On the first profile the new scalar width is larger than the previous 343 bits, but the new attribute blocks are shorter. Neither table includes framing or preprocessing clocks.

### Filtering each side with the entire formula

For a designated side S, branch only on unassigned variables in S, but propagate units from the *whole* residual CNF until fixed point after every branch. Any global witness extending the guesses agrees with each forced bit, including those on the opposite side. Discard contradictions. At the depth bound, construct a relaxation over the surviving S variables: keep residual side-local clauses; if opposite literals z and -z have guarded requests (z or D) and (-z or E) with both guards entirely in S, add the consequence D or E. Skip tautologies. The experiment retains up to four shortest guards of each sign per variable before pairing; this only weakens the filter. Select an incidence forest from the entailed side clauses and count/rank its satisfying assignments by tree messages. Assigned side bits are stored on the path. Opposite bits are deliberately left out of the address.

The terminal domains of siblings are disjoint because their branch bit belongs to S. A full satisfying witness follows one branch and satisfies the forest at every terminal it reaches. Induction gives an injective rank for each retained side assignment and a rank for the restriction of every witness. The two independent projections may retain incompatible pairs. The original terminal predicate still tests the combined assignment including all omitted clauses, hence zero inner product is equivalent to acceptance on every retained pair. Empty projection implies UNSAT. If propagation satisfies all clauses, completion by zeros on the unassigned variables gives a directly checkable residual witness; equivalence of the preprocessing transfers existence to the original input. Respect these public shortcuts before encrypting. Without a shortcut, rank from the given full witness, fetch one ciphertext and one key, and decrypt as usual. On false instances every retained pair rejects, as required by the selective hybrid.

A depth cap bounds tree nodes by 2^(depth+1)-1 per side. Each propagation step sets a fresh variable, each forest has at most the residual clause and generated resolvent count, and forest ranks/counts use integer arithmetic. Limit total nodes and use an ordinary terminal relaxation when the cap is reached. The old one-sided forest and the new domain can be compared per side: both contain all true projections, so the compiler can safely select the smaller cardinality independently on either side. This optional portfolio increases public compilation cost. It has no monotone running-time guarantee.

### Fixed-depth controls

These are exact domain cardinalities at depth 9 on the four-round residuals from PR 93 (or the last completed round). The same deterministic cut, nonrandom tree rule and depth apply across the respective runs. Each cell gives the old local-only forest count followed by the new count. A comparison DPLL probe on the original formula exhausted the sum of the two new tree node counts on every row; neither new tree found a public model at this depth. Matching numbers of nodes does not equate machine time, especially across different residuals.

| Seed and generator | Left ciphertext count | Right key count | Combined tree nodes |
|---|---:|---:|---:|
| 854, planted 540 clauses | 2338081130 → 2184338747 | 179476742856 → 114073270186 | 1716 |
| 1202, uniform 560 clauses | 4791395074 → 1281542062 | 409989393910 → 187886495474 | 1660 |
| 1203, uniform 560 clauses | 4694701500 → 3520388228 | 188772638004 → 205430049234 | 1762 |
| 1204, uniform 560 clauses | 2814184055 → 2278370253 | 928041802496 → 180623717686 | 1652 |
| 1205, uniform 560 clauses | 4621265840 → 2133596570 | 83939828984 → 28214432350 | 1792 |

The key side regresses on seed 1203; use the original key-side forest if choosing by count. Seed 1204 improves the key count by 5.14 times while retaining nonempty domains on both sides. No satisfying assignment or refutation is assumed for seeds 1203–1205. Seed 1202 is the independently refuted NO control from PR 93.

At depth 17 on seed 1202 the new counts are 775542 and 281009968, versus 97128514 and 27454170802 in PR 93. At depth 24 the left count is zero after 4549 nodes, enough to bypass encryption on this public NO instance. PR 93 also refutes it in 3753 ordinary proof-tree nodes. On seed 854, depth 17 gives 8749398 ciphertexts and 123070763 keys as a diagnostic (93.616 PiB combined with pivot deletion); propagation already finds a checkable YES witness at depth 13, so that large table should never be emitted by a dispatcher taking the public shortcut. These are input-dependent results. The construction retains the previous fallback on opaque circuits and no improvement of its worst-case WE machine bound is established.

### Reproduction

Extract the final Python listings from the pinned [PR 93 note](https://github.com/MachinaIO/SigabaPark/blob/121e230357e9154fd838a3bbd5fc74dc9a06dd3b/dag/Notes/pq-we-latent-unit-profiles.md) and [PR 91 note](https://github.com/MachinaIO/SigabaPark/blob/29b7f29db2ea0554e5ea76db6e3bdb4def2b50de/dag/Notes/pq-we-block-dominance.md) as latent.py and profiles.py. Run the first listing as `python coupled.py latent.py profiles.py 9 13 17 20 24`. It also exhausts the side-rank interface on 180 small random formulas and tests the complete two-domain zero predicate against every assignment on another 180 formulas. The second listing uses SymPy for exact integer operations and checks 1792 quotient residuals before and after rounding, including both bits and all predicate/attribute patterns in its toy dimensions.

~~~python
from collections import Counter
from random import Random
import sys, runpy

class Projection:
    def __init__(self, rows, side, depth, lib):
        self.lib = lib
        self.rows = tuple(sorted({tuple(sorted(set(c))) for c in rows if not any(-a in c for a in c)}))
        self.side = sum(1<<(v-1) for v in side)
        self.occ = Counter()
        levels = [0] * (2+max(map(len,self.rows),default=0))
        for i,c in enumerate(self.rows):
            levels[len(c)] |= 1<<i
            for a in c:
                self.occ[a] |= 1<<i
        self.nodes = self.conflicts = self.models = 0
        self.model = None
        self.root = self.visit(tuple(levels),0,0,depth)

    def assign(self, levels, a):
        sat,opp = self.occ[a],self.occ[-a]
        return tuple((level & ~(sat|opp)) | (levels[j+1]&opp if j+1<len(levels) else 0)
                     for j,level in enumerate(levels))

    def visit(self, levels, known, ones, depth):
        self.nodes += 1
        while levels[1] and not levels[0]:
            unit = (levels[1]&-levels[1]).bit_length()-1
            a, = (l for l in self.rows[unit] if not known>>(abs(l)-1)&1)
            bit = 1<<(abs(a)-1)
            known |= bit
            if a>0: ones |= bit
            levels = self.assign(levels,a)
        if levels[0]:
            self.conflicts += 1
            return (0,None)
        remaining = self.side & ~known
        active = sum(levels)
        if not active:
            self.models += 1
            if self.model is None:
                assert self.lib['m']['satisfies'](self.rows,ones)
                self.model=ones
        if not depth or not remaining or not active:
            fs=self.leaf(active,known,remaining)
            vs={i+1 for i in range(remaining.bit_length()) if remaining>>i&1}
            count=self.lib['treecount'](fs,vs)
            return (count,(ones & self.side,vs,fs,None))
        # Prioritize short residual clauses, scoring only admissible branch variables.
        vs = [i+1 for i in range(remaining.bit_length()) if remaining>>i&1]
        def score(v):
            touch = self.occ[v]|self.occ[-v]
            return (sum((level&touch).bit_count() << max(0,8-j) for j,level in enumerate(levels)), -v)
        v=max(vs,key=score)
        bit=1<<(v-1)
        branches=[self.visit(self.assign(levels,a),known|bit,ones|(bit if a>0 else 0),depth-1)
                  for a in (-v,v)]
        return (sum(child[0] for child in branches),(bit,*branches))

    def leaf(self,active,known,remaining):
        # Each pair of opposite guarded requests implies its guard union.
        vs={i+1 for i in range(remaining.bit_length()) if remaining>>i&1}
        local=set(); guards={}
        while active:
            b=active&-active;active-=b
            row=tuple(a for a in self.rows[b.bit_length()-1] if not known>>(abs(a)-1)&1)
            other=[a for a in row if abs(a) not in vs]
            if not other:local.add(row)
            if len(other)==1:
                guards.setdefault(other[0],[]).append(tuple(a for a in row if a!=other[0]))
        for a in sorted(guards):
            if a<0 or -a not in guards:continue
            A=sorted(guards[a],key=lambda c:(len(c),c))[:4]
            B=sorted(guards[-a],key=lambda c:(len(c),c))[:4]
            for c in A:
                for d in B:
                    u=set(c)|set(d)
                    if not any(-l in u for l in u):local.add(tuple(sorted(u)))
        return self.lib['forest'](local,vs)

    def address(self,x,unrank):
        node=self.root
        if unrank and not 0<=x<node[0]:raise ValueError
        offset=0
        while node[1] is not None and len(node[1])==3:
            bit,zero,one=node[1]
            b=(x>=zero[0]) if unrank else bool(x&bit)
            if b:
                if unrank:x-=zero[0]
                else:offset+=zero[0]
            node=one if b else zero
        if node[1] is None:raise ValueError
        fixed,vs,fs,_=node[1]
        free=sum(1<<(v-1) for v in vs)
        if not unrank and ((x&self.side&~free)!=fixed or not all(any(bool(x>>(abs(l)-1)&1)==(l>0) for l in c) for c in fs)):raise ValueError
        leaf=(node[0],False,(fixed,vs,fs))
        z=self.lib['address'](leaf,x,unrank)
        return z if unrank else z+offset

def test(lib):
    rng=Random(913)
    for _ in range(180):
        n=rng.randrange(1,9);V=set(range(1,n+1))
        side={v for v in V if rng.randrange(2)}
        rows=[tuple(v*rng.choice((-1,1)) for v in rng.sample(sorted(V),rng.randrange(min(4,n)+1))) for _ in range(rng.randrange(15))]
        T=Projection(rows,side,rng.randrange(n+1),lib)
        domain=[T.address(j,True) for j in range(T.root[0])]
        assert list(range(len(domain)))==[T.address(x,False) for x in domain]
        models={x&T.side for x in range(1<<n) if all(any(bool(x>>(abs(a)-1)&1)==(a>0) for a in c) for c in rows)}
        assert models<=set(domain)
        for x in range(1<<n):
            if x&~T.side:continue
            try:r=T.address(x,False)
            except ValueError:assert x not in domain
            else:assert domain[r]==x

def test_pairs(lib):
    m=lib['m'];rng=Random(914)
    for _ in range(180):
        n=rng.randrange(1,9);V=set(range(1,n+1))
        left={v for v in V if rng.randrange(2)}
        F=[tuple(v*rng.choice((-1,1)) for v in rng.sample(sorted(V),rng.randrange(min(4,n)+1)))
           for _ in range(rng.randrange(18))]
        T,U=[Projection(F,side,rng.randrange(n+1),lib) for side in (left,V-left)]
        loc,_,cover=m['compile_cnf'](n,F,left)
        for state in range(1<<n):
            yes=m['satisfies'](F,state)
            try: i=T.address(state,False);j=U.address(state,False)
            except ValueError:
                assert not yes
                continue
            x,y=T.address(i,True),U.address(j,True)
            assert (x|y)==state
            vectors=[m['terminal'](cover,k,a,loc) for k,a in enumerate((x,y))]
            assert yes==(sum(a*b for a,b in zip(*vectors))==0)
        if not T.root[0] or not U.root[0]:
            assert not any(m['satisfies'](F,x) for x in range(1<<n))

def benchmark(path93,path91,depths):
    sys.argv=[path93,path91];ns=runpy.run_path(path93); m=ns['m'];test(ns);test_pairs(ns)
    for seed in (854,1202,1203,1204,1205):
        yes=seed==854
        F=m['planted'](128,540,854)[1] if yes else ns['generate'](128,560,seed)
        r,*_=m['project'](F,128,8,0)
        for rr,_ in ns['massage'](r,rounds=4):pass
        rows,_,vs=m['shrink'](rr,set(),128)
        left=ns['fit'](rows,40 if yes else len(vs)//2-3)
        V=set(range(1,len(vs)+1))
        locals_,_,cover=m['compile_cnf'](len(vs),rows,left)
        for depth in depths:
            res=[]
            for side,loc in zip((left,V-left),locals_):
                T=Projection(rows,side,depth,ns)
                for j in {0,T.root[0]//2,T.root[0]-1} if T.root[0] else ():
                    assert T.address(T.address(j,True),False)==j
                old=ns['forest_size'](loc,side,depth)[0] if depth==9 else None
                res.append((T.root[0],T.nodes,T.conflicts,T.models,old))
            ordered=sorted((tuple(sorted(c)) for c in F),key=lambda c:(len(c),c))
            baseline=m['public_probe'](ordered,sum(row[1] for row in res)) if depth==9 else None
            print(seed,len(cover)+2,depth,res,baseline,flush=True)
            if seed>1202:break
if __name__=='__main__':
    benchmark(sys.argv[1],sys.argv[2],list(map(int,sys.argv[3:])))

~~~

~~~python
from itertools import combinations, product
from random import Random
from sympy import Matrix, eye

def check():
    rng=Random(113)
    q=1<<15; step=4
    def matrix(n,m,low,high):
        return Matrix(n,m,lambda i,j:rng.randrange(low,high))
    def roundq(x):
        return (step*((int(x)%q+step//2)//step))%q
    cases=0
    for _ in range(14):
        n=2; a=4; d=4; p=3
        G=Matrix([[1,64,0,0],[0,0,1,64]])
        A0=matrix(n,a,0,q); S=matrix(a,d,-1,2)
        A=A0.row_join(G-A0*S); m=A.cols
        pivot=next(t for t in combinations(range(m),n) if int(A[:,t].det())%2)
        keep=[i for i in range(m) if i not in pivot]
        H=A[:,pivot].T
        inv=H.adjugate()*pow(int(H.det()),-1,q)
        mats=[matrix(n,d,0,q) for i in range(p)]
        masks=[matrix(m,d,-1,2) for i in range(p)]
        for v in product(range(2),repeat=p):
            Cv=sum((i*M for i,M in zip(v,mats)),Matrix.zeros(n,d))
            y=matrix(m+d,1,-2,3);u=A.row_join(Cv)*y
            for w in product(range(2),repeat=p):
                s=matrix(n,1,-2,3);noise=matrix(m,1,-2,3)
                base=A.T*s+noise
                corr=(inv*base[list(pivot),:]).applyfunc(lambda x:x%q)
                base2=base-A.T*corr
                assert all(int(base2[j])%q==0 for j in pivot)
                parts=[(M+wi*G).T*s+T.T*noise for M,wi,T in zip(mats,w,masks)]
                parts2=[c-M.T*corr for c,M in zip(parts,mats)]
                yshort=y[keep+list(range(m,m+d)),:]
                def joined(b,blocks):
                    return b.col_join(sum((i*z for i,z in zip(v,blocks)),Matrix.zeros(d,1)))
                for bit in (0,1):
                    label=u.dot(s)+bit*(q//2)+1
                    target=label-u.dot(corr)
                    prior=label-y.dot(joined(base,parts))
                    after=target-yshort.dot(joined(base2[keep,:],parts2))
                    assert (after-prior)%q==0
                    rounded=roundq(target)-yshort.dot(joined(base2[keep,:].applyfunc(roundq),
                                                             [z.applyfunc(roundq) for z in parts2]))
                    err=int(rounded-prior+q//2)%q-q//2
                    allowed=(step//2)*(1+sum(abs(y[i]) for i in keep)+sum(v)*sum(abs(y[i]) for i in range(m,m+d)))
                    assert abs(err)<=allowed
                    if sum(i*j for i,j in zip(v,w))==0:
                        assert int(q//4<=int(rounded)%q<3*q//4)==bit
                    cases+=1
    return cases
if __name__=='__main__': print(check())

~~~

The following standalone sweep also tests signed-word round trips and exact rounding means on small inputs.

~~~python
from math import isqrt
from itertools import product

def ceildiv(x,y):return (x+y-1)//y
def ceilroot(x):
    r=isqrt(x)
    return r+(r*r<x)
def calc(p,K,C,t,r):
    n=1<<17;e=512;d=n*ceildiv(e,r);M=1<<21
    slack=e+(e-1).bit_length()+2*(384+(p*d).bit_length())
    a=max(n+slack,ceildiv(n*e+slack,t));m=a+d
    if m+1>M:return None
    lg=lambda x:(x-1).bit_length()
    s=r+9+t+ceildiv(lg(p*(m+d+p+400)),2)
    L=m+d;J=L-n;Y2=256*(1<<(2*s))*L
    # Condition on the sampled key. Three errors: base noise, mask noise, wire rounding.
    # For each, enforce 2 exp(-2 threshold^2 / sum widths^2) <= 2^-159
    # using exponent >=160 and e>=2 as the natural exponential base.
    q=1<<e
    lim=q//16
    if 2*lim**2 < 160*32**2*(1+Y2):return None
    if 2*lim**2 < 160*(2<<(t))**2*256*m*p*Y2:return None
    h=0
    while (1<<(2*h)) < 5120*(1+p*Y2):h+=1
    h=min(e,h)
    # Sum the unary high parts after zig-zag, pad each vector to the public slot bound.
    def slot(b):return J*(b+1)+(32*(1<<s)*ceilroot(J*L))//(1<<b)
    keybits,b=min((slot(b),b) for b in range(s+2,s+8))
    ct=1+m-n+p*d
    return (keybits*K+h*ct*C,r,t,s,b,h,m,d,keybits,ct)

if __name__=='__main__':
    for p,K,C in [(1076,209012224,458752),(831,8965806142,79437951),
                  (831,123070763,8749398)]:
        rows=(calc(p,K,C,t,ceildiv(512,k)) for k in range(1,65) for t in range(1,513))
        print(p,min(a for a in rows if a))

def rice_test():
    def encode(values,b):
        out=[]
        for y in values:
            z=2*y if y>=0 else -2*y-1
            out.extend([1]*(z>>b)+[0])
            out.extend((z>>j)&1 for j in range(b))
        return out
    def decode(stream,b,length):
        it=iter(stream);values=[]
        for _ in range(length):
            high=0
            while next(it):high+=1
            z=(high<<b)+sum(next(it)<<j for j in range(b))
            values.append(z//2 if not z%2 else -(z//2)-1)
        return values
    for b in range(1,5):
        for ys in product(range(-4,5),repeat=3):
            bits=encode(ys,b)
            assert decode(bits+[0]*13,b,len(ys))==list(ys)
            assert len(bits)<=len(ys)*(b+1)+(2*ceilroot(len(ys)*sum(y*y for y in ys)))//(1<<b)
    for value in range(32):
        lo,r=divmod(value,8)
        errors=[8*(lo+(z<r))-value for z in range(8)]
        assert sum(errors)==0 and max(errors)-min(errors)<=8
if __name__=='__main__':rice_test()

~~~
