---
title: Rank-adaptive existential elimination of Boolean witness columns
refs: [definition:WE_CircuitSAT_Capped, definition:ColumnElimination, theorem:AdvancedEncryption.WE.ColumnElimination.variable_rank, theorem:AdvancedEncryption.WE.ColumnElimination.first_one_valid, theorem:AdvancedEncryption.WE.ColumnElimination.backsolve_remainder, theorem:AdvancedEncryption.WE.ColumnElimination.backsolve_length, note:pq-we-symbolic-slices]
tags: [circuit-sat, witness-encryption, elimination, affine-subspaces]
---

A mixed 128-input, 4096-NAND circuit admits a registered child using 80 input bits. The rank of a local three-column system takes each value from zero through three as the retained bits vary. Symbolic elimination yields 3420 live NANDs, and small-component synthesis yields 238. A second route works with arbitrarily high degree on the retained variables, without truth-table enumeration or expanding their ANFs. A 96-variable example with 3^48 terms if expanded compiles to 238 live NANDs. Both methods project a satisfying witness and reconstruct a full witness from any accepting child input.

### Extracting an affine block from registered gates

Normalize every self or forward reference to the constant-true wire before analyzing dependencies. One implementation computes capped exact ANFs, cancelling duplicated squarefree monomials over GF(2), and recognizes the four-NAND XOR identity even when its intermediate products exceed the cap. To require the final gate to output one, stop at a certified polynomial, flip a required bit through a duplicated-input NAND, or replace a required zero NAND by the conjunction of its two required-one operands. Memoize (wire,required bit) to preserve sharing. Reject an unresolved disjunctive demand. Row-reducing the vector-valued ANF guards by constant binary row operations preserves their joint zero set and can separate physically mixed equations. Put an edge between every pair of input variables appearing in the same monomial of a retained equation. A deterministically constructed independent set S then makes each equation jointly affine in its selected variables b. Inspect every monomial for at most one selected variable. A maximum independent set is unnecessary. Neither a small per-variable degree nor affinity in each variable separately would suffice.

On a second route, try a public candidate S (the example uses a fixed prefix of 32). Carry pairs (c,u) representing c(y)+Σ_i u_i(y)b_i, whose bits are IDs in a shared, hash-consed Boolean DAG. An unrestricted y-only subcircuit has zero slope. XOR adds termwise. In a product the constant is cd, the i slope is c v_i+d u_i+u_i v_i, and the ij coefficient is u_i v_j+u_j v_i. Require the two terms of every cross coefficient to have identical computed IDs after simplification. NAND toggles the constant. A missing structural identity makes the gate unknown; it is never taken as a proof of inequality or of zero. At the output use the same exact demand-peeling rules. This path can handle high-degree coefficients even when intermediate ANFs vastly exceed the monomial budget. Candidate blocks can be tried in a fixed list subject to a global cap. The typed statement supplies no auxiliary cut.

### Projection and reconstruction

At a fixed y the guard requires Σ_j a_j b_j = t, with the constant vector as target t. Let l read the first nonzero coordinate of a, or be zero when the column is zero. Apply P(v)=v−l(v)a to the target and to all subsequent columns. Over GF(2), subtraction is XOR. A zero column acts as the identity. Otherwise P kills a, and its kernel is exactly the span of a. More explicitly, if P(u)=P(t), then t=(l(t)−l(u))a+u. Applying this identity to any combination of subsequent columns proves the one-step existential equivalence. Repeating proves that the final target vanishes exactly when the original system is consistent. This is pointwise in y: none of the pivots, pivot indices or ranks have to be fixed across the witness space. Unlike a fixed isotropic slice or symbolic row masker, this construction emits a deterministic child predicate and has no ciphertext masks or projection-hiding premise.

For projection delete S from the witness and pack the retained coordinates in increasing order. To lift, recreate each current pivot and transformed suffix at the supplied y, then back-substitute the scalar l(t_i−Σ_{j>i}a_j^{(i)}b_j) in reverse order. The Lean reconstruction proves an equality even on rejecting targets: the original target minus the weighted reconstructed columns after the initial linear map equals the final remainder. It also proves that the scalar list has exactly the input-column length. The variable-rank equivalence is proved for arbitrary normalized selectors over a field; firstOne separately discharges normalization for every binary column, including the empty row set. On a compatible y there are 2^(|S|−rank A(y)) lifts. Thus the compiler preserves existence, not the number or uniform distribution of witnesses.

### Emitting a registered child

All working matrix entries and the target use a single numbering of retained input coordinates and shared NAND/negation nodes. For a column a define sel_i = a_i times the product of previous (1+a_h). At most one selection bit is one, so each l(v) can be computed as an OR of the sel_i AND v_i. For the first output row, v'_0=v_0 AND NOT a_0; the remaining rows use XOR with a_i AND l(v). These two identities brought the symbolic child below 4096 gates on the mixed fixture. Duplicate monomials are cancelled during polynomial multiplication; shared coefficients, gates, complemented literals, and repeated scalar constraints are reused or reduced. The live root cone is renumbered once. For a small disconnected component, an optional method tabulates consistency on just its own retained bits and emits a Shannon DAG. If one side of the table equals an affine coset, derive independent checks by testing parity constraints and prove equality by dimension and cardinality before emitting them instead. All local coordinate indices use the same global packing. The baseline directly tests only 16·32 component systems on the mixed case and combines independently chosen lifts. It can decide this particular instance without child encryption.

Pad the live circuit with unreachable NAND(0,0) gates before its final defining gate, or use a double negation when the output is an input. A registered child always has 128 physical input positions and 4096 gates. Dec projects to the first |y| positions and pads with arbitrary fixed bits. The child ignores surplus bits even if an adversary or witness supplier sets them arbitrarily. Emit only if the live-root construction fits; an identity branch can keep the original statement at caps or unsupported guards. In particular, no gate addresses in the emitted child rely on forward references.

| Source and method | Retained witness bits | Live NANDs before padding | Exact statement encoding bits after padding |
| --- | ---: | ---: | ---: |
| Mixed source (2798 construction gates) | 128 | 2798 construction gates | 56,516,462 |
| Dynamic column elimination | 80 | 3420 | 33,550,732 |
| Component truth tables | 80 | 318 | 409,106 |
| Component affine-complement detection | 80 | 238 | 260,198 |
| High-degree source | 128 | — | 95,075,746 |
| High-degree symbolic child | 96 | 238 | 250,902 |

The source columns in the mixed fixture give three equations per eight raw variables with 384 XOR row mixes over the 48 equations. Independent-set elimination removes three variables in each component. Among its 32 possible y values, the local ranks 0,1,2,3 occur 1,3,12,16 times. The only incompatible y values are 0 and 17. The original has 56^16 witnesses, the packed child 30^16 accepting coordinates, and the registered child additionally admits 2^48 arbitrary unused-bit fillings for each. Each local source assignment and all 32 single-component replacements in the global registered child were checked. Random satisfying lifts and out-of-domain examples were replayed on the raw source and all three padded children.

For a separate sparse case require b_i y_i=1 for all 64 pairs. Only the all-one original witness works, and the child requires all 64 retained bits, using 126 live NANDs. An additional zero constraint on its first y is contradictory; the tabulated child is the single constant-false NAND. In the high-degree test require b_i H(y)=1 for 32 b bits, where H is the conjunction of the OR of each of 48 disjoint pairs. The rank is 32 when H=1 and zero otherwise. The structural route builds 287 shared gates including intermediates, producing the 238-gate live child; both branches were replayed, including arbitrary high child witness bits and generic reverse substitution. The test enumerates all binary matrices and targets of shapes 2×3 and 3×2 and checks compatibility, explicit lifts and exact fiber counts.

### Cost and the remaining WE obligation

For m equations and k candidate columns, a dense symbolic step builds O(m) selectors and O(m) gate operations for each remaining column or target. The full elimination costs O(m k(k+1)) word-level circuit operations, in addition to coefficient generation, hash-consing, live-cone packing and witness maps. Back-substitution stores per-step data; the implementation can instead store just the selector's evaluation of the current target and each suffix column. The structural product check can take O(k²) node comparisons per raw gate; the dense route guards its work by m(k+1)². Sparse ANF products, RREF over monomial coefficients, connected components and local truth-table costs must be counted separately. The compilers can return unknown on an operation/node budget rather than expand an uncontrolled shared cone. Choosing an enumeration limit h for a component bounds its consistency table at 2^h evaluations. The encrypted child still carries a padded registered statement. One encoded gate with ordered indices a,b costs 4a+2b+3 bits: unary indices, inner framing of the first coordinate, and outer list framing. The table gives exact counts for the resulting gate lists, before external algorithm tuple framing.

For a direct SAT branch the sender can return its bit unchanged on YES and a fixed value on NO, with the corresponding public decoder. For a child-WE branch Enc returns the child ciphertext verbatim; valid original witnesses project to valid child witnesses, and a false original has a false child by the lift theorem. In the registered security game the attacker's tuple contains the *original* statement. A reduction taking the child challenge must reconstruct or hardwire the original statement, and pay the corresponding time and description overhead. Equality of ciphertext laws alone does not certify the same tight finite cost/gain bound at 128 bits. An identity fallback using an existing full WE can on its branch preserve the complete challenge and attacker unchanged. The budgets include both algorithm time maxima and both canonical descriptions even when preprocessing declines. No registered Machine implementation, strict 2^32 certificate, 2^100 general construction or independently secure sparse backend follows from this gate-count ledger.

### Standalone replay

```python
from random import Random
from itertools import combinations,product
def extract(g,degree=3):
    n=128;refs=[None]*129;xyz=[None]*129
    polys=[{0}]+[{1<<i} for i in range(n)]
    for a,b in g:
        i=len(refs);a=a if a<i else 0;b=b if b<i else 0
        refs.append((a,b));xor=None
        if refs[a] and refs[b]:
            for s in set(refs[a])&set(refs[b]):
                if refs[s] is None:continue
                x=refs[a][0]^refs[a][1]^s;y=refs[b][0]^refs[b][1]^s
                if sorted(refs[s])==sorted((x,y)):xor=(x,y);break
        xyz.append(xor)
        p,q=polys[a],polys[b]
        if xor is not None:
            x,y=xor;r=polys[x]^polys[y] if polys[x] is not None and polys[y] is not None else None
        elif a==b:r={0}^p if p is not None else None
        elif p is not None and q is not None and len(p)*len(q)<=10000:
            r={0}
            for x in p:
                for y in q:r.symmetric_difference_update((x|y,))
        else:r=None
        polys.append(r if r is None or (len(r)<=10000 and all(k.bit_count()<=degree for k in r)) else None)
    work=[(len(refs)-1,1)];guards=[];seen=set()
    while work:
        i,bit=work.pop()
        if (i,bit) in seen:continue
        seen.add((i,bit));p=polys[i]
        if p is not None:
            guards.append(p^({0} if bit else set()));continue
        a,b=refs[i]
        if a==b:work.append((a,bit^1))
        elif not bit:work.extend(((a,1),(b,1)))
        else:raise ValueError('unresolved')
    return guards
def basis(rows):
    table = {}
    for row in rows:
        p = set(row)
        while p and max(p) in table:
            p ^= table[max(p)]
        if p:
            table[max(p)] = p
    for lead in sorted(table):
        for other in table:
            if lead < other and lead in table[other]:
                table[other] ^= table[lead]
    return table


def raw():
    g=[]; G=[]
    def nand(i,j): g.append((i,j));return 128+len(g)
    def inv(i):return nand(i,i)
    def prod(i,j):return inv(nand(i,j))
    def xor(i,j):
        t=nand(i,j);return nand(nand(i,t),nand(j,t))
    for k in range(16):
        b,c,d,y,z,u,v,w=range(1+8*k,9+8*k)
        y,z,u,v=map(inv,(y,z,u,v))
        for t,q,r,h,i,j in [(y,z,u,y,z,w),(z,u,v,z,u,v),(u,v,w,y,v,w)]:
            G.append(xor(xor(prod(b,t),prod(c,q)),xor(prod(d,r),prod(h,prod(i,j)))))
    rng=Random(161)
    for _ in range(384):
        a,b=rng.sample(range(len(G)),2);G[a]=xor(G[a],G[b])
    x=inv(G[0])
    for a in G[1:]:x=prod(x,inv(a))
    used=len(g);last=g.pop();g.extend([(4224,4224)]*(4095-len(g)));g.append(last)
    return g,used
def ones(w):
    while w:
        t=w&-w;yield t.bit_length()-1;w^=t

def evalpoly(p,w):
    return sum(w&m==m for m in p)%2

def run(g,w):
    x=[1]+[(w>>i)&1 for i in range(128)]
    for i,j in g:
        x.append(1^((x[i] if i<len(x) else 1)&(x[j] if j<len(x) else 1)))
    return x[-1] if g else 1

class Net:
    def __init__(self,limit=100000):
        self.limit=limit
        self.g=[];self.cache={};self.neg={}
        self.T=0;self.F=self.raw(0,0)
        self.neg.update({self.T:self.F,self.F:self.T})
    def raw(self,a,b):
        pair=tuple(sorted((a,b)))
        if pair not in self.cache:
            if len(self.g)>=self.limit:raise OverflowError("NAND construction cap")
            self.g.append(pair);self.cache[pair]=128+len(self.g)
        return self.cache[pair]
    def inv(self,x):
        if x not in self.neg:
            y=self.raw(x,x);self.neg[x]=y;self.neg[y]=x
        return self.neg[x]
    def mul(self,a,b):
        if self.F in (a,b) or self.neg.get(a)==b:return self.F
        if a==self.T:return b
        if b==self.T or a==b:return a
        return self.inv(self.raw(a,b))
    def either(self,a,b):
        return self.inv(self.mul(self.inv(a),self.inv(b)))
    def xor(self,a,b):
        if a==b:return self.F
        if self.neg.get(a)==b:return self.T
        if a==self.F:return b
        if b==self.F:return a
        if a==self.T:return self.inv(b)
        if b==self.T:return self.inv(a)
        t=self.raw(a,b)
        return self.raw(self.raw(a,t),self.raw(b,t))
    def reduce(self,terms,multiply=False):
        a=self.T if multiply else self.F
        for x in terms:a=self.mul(a,x) if multiply else self.xor(a,x)
        return a
    def mux(self,c,l,h):
        if l==h:return l
        if (l,h)==(self.F,self.T):return c
        if (l,h)==(self.T,self.F):return self.inv(c)
        if l==self.F:return self.mul(c,h)
        if h==self.F:return self.mul(self.inv(c),l)
        if l==self.T:return self.either(self.inv(c),h)
        if h==self.T:return self.either(c,l)
        if self.neg.get(l)==h:return self.xor(c,l)
        return self.raw(self.inv(self.mul(c,h)),self.inv(self.mul(self.inv(c),l)))
    def packed(self,root):
        live=set();todo=[root]
        while todo:
            i=todo.pop()
            if i<=128 or i in live:continue
            live.add(i);todo.extend(self.g[i-129])
        g=[];ids={}
        for i in sorted(live):
            g.append(tuple(ids.get(a,a) for a in self.g[i-129]));ids[i]=128+len(g)
        out=ids.get(root,root)
        if g and out==128+len(g):tail=g.pop()
        else:
            g.append((out,out));tail=(128+len(g),)*2
        size=len(g)+1
        return (g+[(0,0)]*(4095-len(g))+[tail] if size<=4096 else None),size

def group(rows):
    groups=[]
    for p in rows:
        used=0
        for m in p:used|=m
        r=[p];other=[]
        for mask,ps in groups:
            if mask&used:used|=mask;r+=ps
            else:other.append((mask,ps))
        groups=other+[(used,r)]
    return groups

def greedy(rows):
    graph=[0]*128
    for p in rows:
        for m in p:
            for i in ones(m):graph[i]|=m^(1<<i)
    S=0
    for i,v in enumerate(graph):
        if not S&v:S|=1<<i
    assert all((S&m).bit_count()<=1 for p in rows for m in p)
    return S

def split(rows,S):
    variables=list(ones(S))
    rhs=[{m for m in p if not m&S} for p in rows]
    cols=[[{m^(1<<i) for m in p if m>>i&1} for p in rows] for i in variables]
    return variables,rhs,cols

def numerical(rhs,cols,y):
    T=sum(evalpoly(p,y)<<j for j,p in enumerate(rhs))
    A=[sum(evalpoly(p,y)<<j for j,p in enumerate(col)) for col in cols]
    return solve_vectors(T,A)

def solve_vectors(T,A):
    A=list(A);steps=[];rank=0
    for j,a in enumerate(A):
        l=a&-a;rank+=bool(l)
        steps.append((l,T,A[j+1:]))
        for k in range(j+1,len(A)):
            if l&A[k]:A[k]^=a
        if l&T:T^=a
    if T:return False,0,rank
    b=0
    for j in reversed(range(len(steps))):
        l,t,tail=steps[j]
        for k,c in enumerate(tail,j+1):
            if b>>k&1:t^=c
        if t&l:b|=1<<j
    return True,b,rank

def tree(net,ys,f):
    a=list(f)
    for y in ys:a=[net.mux(y,a[i],a[i+1]) for i in range(0,len(a),2)]
    return a[0]

def project_net(net,T,A):
    for j,a in enumerate(A):
        pref=net.T;sel=[]
        for h in a:
            sel.append(net.mul(pref,h));pref=net.mul(pref,net.inv(h))
        def update(v):
            dot=net.F
            for x,y in zip(sel,v):dot=net.either(dot,net.mul(x,y))
            return [net.mul(v[0],net.inv(a[0]))]+[net.xor(x,net.mul(u,dot)) for x,u in zip(v[1:],a[1:])]
        for k in range(j+1,len(A)):A[k]=update(A[k])
        T=update(T)
    return T

def affine_table(net,ys,table):
    universe=1<<len(ys)
    for value in (net.F,net.T):
        pts=[i for i,v in enumerate(table) if v==value]
        if not pts:return net.T if value==net.F else net.F
        if len(pts)&(len(pts)-1):continue
        pivot={};rows=[]
        for mask in sorted(range(1,universe),key=int.bit_count):
            offset=(mask&pts[0]).bit_count()%2
            if not all((mask&p).bit_count()%2==offset for p in pts):continue
            v=mask
            while v and (i:=v.bit_length()-1) in pivot:v^=pivot[i]
            if v:pivot[v.bit_length()-1]=v;rows.append((mask,offset))
        if len(pts)!=1<<(len(ys)-len(rows)):continue
        guards=[]
        for mask,offset in rows:
            f=net.reduce([ys[i] for i in ones(mask)])
            guards.append(f if offset else net.inv(f))
        inside=net.reduce(guards,True)
        return net.inv(inside) if value==net.F else inside
    return tree(net,ys,table)

def compiler(g,method='pivot',small=8):
    rows=list(basis(extract(g)).values())
    S=greedy(rows);Y=list(ones(((1<<128)-1)^S))
    idx={a:j+1 for j,a in enumerate(Y)};net=Net()
    def project(w):return sum(((w>>j)&1)<<i for i,j in enumerate(Y))
    pieces=[];tests=[]
    for mask,rs in group(rows):
        bs,rhs,cols=split(rs,S&mask)
        ys=list(ones(mask&~S))
        pieces.append((bs,rhs,cols))
        if method in ('local','affine') and len(ys)<=small:
            truth=[]
            for v in range(1<<len(ys)):
                y=sum(((v>>i)&1)<<j for i,j in enumerate(ys))
                ok,_,_=numerical(rhs,cols,y);truth.append(net.T if ok else net.F)
            lower=affine_table if method=='affine' else tree
            tests.append(lower(net,[idx[a] for a in ys],truth))
            continue
        mon={0:net.T}
        pol={}
        def emit(p):
            key=tuple(sorted(p))
            if key not in pol:
                for m in key:
                    if m not in mon:mon[m]=net.reduce([idx[i] for i in ones(m)],True)
                pol[key]=net.reduce([mon[m] for m in key])
            return pol[key]
        T=list(map(emit,rhs));A=[list(map(emit,col)) for col in cols]
        T=project_net(net,T,A)
        tests.extend(net.inv(v) for v in T)
    child,L=net.packed(net.reduce(tests,True))
    def lift(v):
        w=sum(((v>>i)&1)<<j for i,j in enumerate(Y))
        for bs,rhs,cols in pieces:
            ok,b,_=numerical(rhs,cols,w)
            if not ok:return None
            w|=sum(((b>>i)&1)<<j for i,j in enumerate(bs))
        return w
    return rows,S,Y,child,L,project,lift

def unique(bad=False):
    g=[]
    def nand(i,j):g.append((i,j));return 128+len(g)
    def and_(i,j):
        q=nand(i,j);return nand(q,q)
    a=0
    for i in range(64):a=and_(a,and_(2*i+1,2*i+2))
    if bad:a=and_(a,nand(2,2))
    last=g.pop();return g+[(4224,4224)]*(4095-len(g))+[last]

def exhaustive():
    for m,r in [(2,3),(3,2)]:
        for cols in product(range(1<<m),repeat=r):
            for rhs in range(1<<m):
                def bits(x):return [{0} if x>>j&1 else set() for j in range(m)]
                ok,b,rank=numerical(bits(rhs),[bits(x) for x in cols],0)
                sols=[]
                for w in range(1<<r):
                    v=rhs
                    for j,c in enumerate(cols):
                        if w>>j&1:v^=c
                    if not v:sols.append(w)
                assert ok==bool(sols)
                if ok:assert b in sols and len(sols)==1<<(r-rank)

def audit():
    exhaustive()
    rng=Random(163)
    g,used=raw()
    r,S,Y,c,L,project,lift=compiler(g)
    _,_,_,local,D,_,_=compiler(g,'local')
    _,_,_,flat,F,_,_=compiler(g,'affine')
    assert len(c)==len(local)==len(flat)==len(g)==4096 and len(Y)==80 and len(r)==48
    selected=[8*j+k for j in range(16) for k in range(3)]
    assert list(ones(S))==selected
    legal=[]
    for j in range(16):
        sub=[p for p in r if all(m&~(255<<(8*j))==0 for m in p)]
        bs,t,a=split(sub,S&(255<<(8*j)))
        count=0;dst=[];ranks={}
        for v in range(32):
            y=(8*v)<<(8*j);ok,b,rk=numerical(t,a,y);ranks[rk]=ranks.get(rk,0)+1
            old=[w for w in range(8) if all(not evalpoly(p,y|(w<<(8*j))) for p in sub)]
            assert ok==bool(old) and (not ok or b in old and len(old)==1<<(3-rk))
            if ok:dst.append(v);count+=len(old)
        assert count==56 and [u for u in range(32) if u not in dst]==[0,17]
        legal.append(dst)
    for _ in range(128):
        w=rng.getrandbits(128)
        assert run(g,w)==(not any(evalpoly(p,w) for p in r))
        for y in (rng.getrandbits(80),sum(rng.choice(v)<<(5*j) for j,v in enumerate(legal))):
            w=lift(y);ok=w is not None
            assert run(c,y)==run(local,y)==run(flat,y)==ok
            if ok:assert project(w)==y and run(g,w)
    for j in range(16):
        for yy in range(32):
            assignment=sum((yy if k==j else legal[k][0])<<(5*k) for k in range(16))
            assert run(c,assignment)==run(local,assignment)==run(flat,assignment)==(yy in legal[j])
    print('unframed statement lengths mixed source/pivot/local',enc_size(g),enc_size(c),enc_size(local),enc_size(flat))
    print('variable rank: raw',used,'guards',len(r),'retained',len(Y),'symbolic/local/local-affine NANDs',L,D,F,'local ranks',ranks)
    for bad in (False,True):
        u=unique(bad)
        for method in ('pivot','local'):
            rows,s,ys,ct,d,proj,back=compiler(u,method)
            assert ct is not None
            for v in [0,(1<<len(ys))-1]+[rng.getrandbits(len(ys)) for _ in range(16)]:
                w=back(v)
                assert run(ct,v)==(w is not None)==(v==(1<<len(ys))-1 and not bad)
                if w is not None:assert w==(1<<128)-1 and run(u,w)
            print('unique fixture contradictory',bad,method,'free',len(ys),'child gates',d)
def structural(g,B,limit=100000):
    """Exact affine-in-B dataflow. Coefficients are arbitrary NAND DAGs on y."""
    Y=[i for i in range(128) if i not in B]
    yidx={x:j+1 for j,x in enumerate(Y)}
    net=Net(limit)
    # Store base and nonzero slope nodes. certify(r) never treats unknown as zero.
    value=[(net.T,{})]+[(net.F,{i:net.T}) if i in B else (yidx[i],{}) for i in range(128)]
    ref=[None]*129
    def combine(x,y,XOR):
        if x is None or y is None:return None
        c,u=x;d,v=y
        keys=sorted(u.keys()|v.keys())
        if XOR:
            t={i:net.xor(u.get(i,net.F),v.get(i,net.F)) for i in keys}
            return net.xor(c,d),{i:h for i,h in t.items() if h!=net.F}
        for i,j in combinations(keys,2):
            a=net.mul(u.get(i,net.F),v.get(j,net.F))
            b=net.mul(u.get(j,net.F),v.get(i,net.F))
            if a!=b:return None
        t={}
        for i in keys:
            a,b=u.get(i,net.F),v.get(i,net.F)
            h=net.reduce([net.mul(c,b),net.mul(d,a),net.mul(a,b)])
            if h!=net.F:t[i]=h
        return net.inv(net.mul(c,d)),t
    for a,b in g:
        pos=len(ref)
        a=a if a<pos else 0;b=b if b<pos else 0
        xx=None
        if ref[a] is not None and ref[b] is not None:
            for mid in set(ref[a])&set(ref[b]):
                if ref[mid] is None:continue
                i=ref[a][0]^ref[a][1]^mid;j=ref[b][0]^ref[b][1]^mid
                if sorted(ref[mid])==sorted((i,j)):xx=i,j;break
        if a==b and value[a] is not None:
            u,p=value[a];out=net.inv(u),p
        elif xx is None:out=combine(value[a],value[b],False)
        else:out=combine(value[xx[0]],value[xx[1]],True)
        value.append(out);ref.append((a,b))
    todo=[(len(ref)-1,1)];seen=set();guards=[]
    while todo:
        i,bit=todo.pop()
        if (i,bit) in seen:continue
        seen.add((i,bit))
        if value[i] is not None:
            c,p=value[i];guards.append((net.inv(c) if bit else c,p))
        else:
            a,b=ref[i]
            if a==b:todo.append((a,1-bit))
            elif not bit:todo.extend(((a,1),(b,1)))
            else:raise ValueError('uncertified disjunctive guard')
    guards=list({(c,tuple(sorted(p.items()))):(c,p) for c,p in guards}.values())
    S=sorted(B)
    T=[c for c,_ in guards]
    A=[[p.get(i,net.F) for _,p in guards] for i in S]
    if len(guards)*(1+len(S))**2>200000:raise OverflowError('dense projection cap')
    original_T=T[:];original_A=[col[:] for col in A];prefix=net.g[:]
    def lift(w):
        y=[1]+[(w>>i)&1 for i in range(128)]
        for a,b in prefix:y.append(1^(y[a]&y[b]))
        t=sum(y[v]<<i for i,v in enumerate(original_T))
        cols=[sum(y[v]<<i for i,v in enumerate(col)) for col in original_A]
        ok,b,_=solve_vectors(t,cols)
        if not ok:return None
        return (sum(((w>>i)&1)<<j for i,j in enumerate(Y)) |
                sum(((b>>i)&1)<<j for i,j in enumerate(S)))
    T=project_net(net,T,A)
    child,L=net.packed(net.reduce([net.inv(t) for t in T],True))
    return child,L,len(guards),len(net.g),Y,lift

def structural_fixture():
    G=[]
    def nand(a,b):G.append((a,b));return 128+len(G)
    def inv(a):return nand(a,a)
    def and_(a,b):return inv(nand(a,b))
    def or_(a,b):return nand(inv(a),inv(b))
    h=0
    for i in range(32,128,2):h=and_(h,or_(i+1,i+2))
    gs=[and_(i+1,h) for i in range(32)]
    x=gs[0]
    for t in gs[1:]:x=and_(x,t)
    last=G.pop();return G+[(4224,4224)]*(4095-len(G))+[last]

def identity_or_child(g,node_limit):
    try:
        ct,L,_,_,_,_=structural(g,set(range(32)),node_limit)
        if ct is not None:return 'child',ct
    except (ValueError,OverflowError):pass
    return 'identity',g

def struct_test():
    g=structural_fixture();c,L,m,allocated,Y,lift=structural(g,set(range(32)))
    assert c is not None and Y==list(range(32,128))
    rng=Random(163)
    for _ in range(64):
        y=sum(rng.choice((1,2,3))<<(2*j) for j in range(48))
        for u in (y,y&~3,rng.getrandbits(96)):
            ok=all(u>>(2*j)&3 for j in range(48))
            assert run(c,u)==run(g,(u<<32)|((1<<32)-1))==ok
            assert not run(g,u<<32)
            packed=u|(rng.getrandbits(32)<<96)
            w=lift(packed)
            assert (w is not None)==run(c,packed)==ok
            if w is not None:assert run(g,w) and w>>32==u
    mode,same=identity_or_child(g,2)
    assert mode=='identity' and same is g
    print('high-degree structural guard: rows',m,'packed residual',L,'allocated gates',allocated)
    print('unframed statement lengths: high-degree source/child',enc_size(g),enc_size(c))

def enc_size(g):
    return sum(4*a+2*b+3 for a,b in g)

if __name__=='__main__':audit();struct_test()

```
