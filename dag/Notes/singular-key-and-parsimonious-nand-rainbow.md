---
title: Singular projection keys and a parsimonious NAND rainbow transfer
refs: [definition:WE_CircuitSAT_Capped, definition:SparseRainbowProjection, theorem:SparseRainbowProjection.fullBadBankCount]
tags: [witness-encryption, matching, linear-algebra]
---

# Singular projection keys and a parsimonious NAND rainbow transfer

The predecessor #258 provided a dense determinant-sign congruence key for suitable planar matching representations. Here a generic public projection yields an exact statistical distance for arbitrary singular field matrices, and a new circuit-specific path cofactor gives a single fixed sink mask with exact privacy. The construction below handles every forward-evaluated NAND circuit mathematically. Its raw cost depends exponentially on live-wire width. This is a restricted cost result for the registered 128-input, 4096-gate problem.

## Complete transcript of a projection bank

Fix a finite field of order q, an n by n matrix M of nullity d, and distinct scalar payloads. Publish independent uniform linear forms h_1,...,h_r, independent uniform u_i images y_i=M u_i, and t=beta+sum h_i(u_i). The forms and images together are independent of beta. Given those public values the secrets are independent uniform points in their affine fibers. If any h_i is nonzero on ker M, normalize a kernel vector v to h_i(v)=1. Translating that u_i by (beta_0-beta_1)v bijects entire tapes with identical output. Otherwise the sum is determined by the images and the two conditional scalar supports are disjoint. There are q^(n-d) bad forms out of q^n since they factor through the quotient. Thus TV of the full output equals q^(-rd), including r=0 or d=0. The formal node proves the corresponding exact cardinality identity, conditional disjointness and the normalized translation. Exhaustive counters below independently check the complete transcript, including h.

For independent repetitions of the same bit in separate banks, any revealed bit separates supports, and when every bank hides the bit the joint laws agree. For fixed matrices the resulting distance is 1-product_j(1-q^(-r_j d_j)). For public randomized matrices condition on their complete public coins first. If matrices and tapes are independent across banks the same formula uses the averaged bad probabilities. Without independence the union bound still applies when the conditional tape laws retain the stated coupling. A simulator using the beta=0 law achieves the indicated distance to beta=1. An invertible bank recovers all u_i by linear solves; the decoder may publicly test invertibility and choose one. Publishing one bank of n by n sparse M costs (2rn+1) field elements plus M's public generation coins, r sparse products and rn evaluations of coefficient-times-input for the dot products. The independent h_i,u_i need 2rn field elements of random tape. Compared with dense #258 congruence, no random invertible basis or dense congruence product is needed; for r comparable to n there need not be a communication saving. These are arithmetic counts.

For an ordinary bipartite matching, sample independent scalar weights for every edge (distinct variables even for parallel edges), summing parallel contributions to one matrix entry. The Edmonds determinant has a nonzero polynomial precisely when a matching exists because distinct matchings use distinct edge monomials. For a general loopless graph place each weight once in a Tutte alternating matrix and its signed transpose. Its Pfaffian has the same monomial property and the determinant is its square. With m edges per matching the nonzero polynomial has degree m in either case. A uniform evaluation misses with probability at most min(1,m/q), by induction on the last variable and the univariate root bound. Independent parallel banks raise this YES failure bound to their number; structural NO always gives singular matrices. GF(2^b) uses b fair bits per scalar. One independent scalar per original edge per bank is sufficient, not per symmetric pair of entries. Ordinary matching ignores the color constraint below.

## From gates to triples, with both witness directions

Take wire 0 as true, primary wires 1 through n and gate i's output n+i (one-based gate i). A parent outside the prior wire list reads true and is normalized to 0. Make distinct occurrences for both reads and the output of each gate, one free unary test of each primary (including unused inputs), and unary true pins on the constant and final output. There are L=3g+n+2 occurrences. Use two different colors (o,0),(o,1) per occurrence. Construct a bipartite multigraph with 2L vertices on each side, and let color be the third part of the triple system. For each wire's cyclically ordered list o_j, connect a left vertex X_j to Y_j colored (o_j,1) and to Y_(j+1) colored (o_j,0). A matching either uses all diagonals (wire value 0) or all shifts (value 1), since occupying Y_j fixes the next choice around the cycle. At size one the two edges are distinct triples. Exactly the colors (o_j,wire value) remain available.

Each gate has three additional left/right aligned slot pairs numbered 0,1,2. Connect the two vertices of each slot by a parallel edge for every eligible occurrence color. At input x the allowed slots are {0} for 0 and {1} for 1. At input y they are {0,1} and {2}. At output z they are {0} and {1,2}. Direct enumeration gives exactly one slot permutation for legal rows 001,011,101,110, and zero for all other rows (also Lean checked). A unary slot takes either occurrence color for a free test or only the 1-color for a pin. Thus rainbow perfect matchings correspond bijectively to accepted primary assignments. Recover the primary bits from the cycles. Conversely evaluate once and take the unique local slot permutation. Repeated, unused and normalized-forward parents are allowed. The graph has 2L colors, 2L left and right vertices, and 2L+8g+2n+2 edges. For the registry instance these counts give 24,836 colors and 57,862 edges. Construction and certificate conversion require O(g+n) records in a RAM model after parsing.

## Color coefficient and the representation boundary

Work over K[(Z/2)^k] in characteristic two with generators z_j^2=1. Sum the edge weights times z_color in each matrix entry. Every determinant term has k edges, so its color exponent equals all ones iff all k colors occur exactly once. The target coefficient therefore equals the weighted sum of rainbow perfect matchings. Independent edge indeterminates prevent formal cancellation. At a sampled point cancellation is possible. For this particular reduction it suffices to put t_i only on one designated shifted edge of primary wire i and assign all other weights one. The exact polynomial is P(t)=sum_{accepted x} product_{i:x_i=1} t_i, since extension multiplicities are one. Its monomials are distinct, its degree is at most n, and it is identically zero on every NO circuit. For n=128 and GF(65536) one bank misses a YES with probability at most 1/512; fifteen independent banks give 2^-135. This takes 128 independent field weights per bank versus 57,862 for the generic scheme on this graph. Tests use the irreducible polynomial 0x1100b.

Testing invertibility over the group algebra, or taking its regular-representation matrix, does not extract this coefficient. Writing z_i=1+e_i gives nilpotent e_i^2=0; the augmentation ideal is nilpotent and units are exactly elements of nonzero augmentation. A diagonal pair of forced color-1 edges gives 1, a unit with zero target coefficient. One forced color-0 slot and one free choice of color 0 or 1 give 1+z_0 z_1 with nonzero target coefficient and zero augmentation. Polynomial signs disappear in characteristic two. A serial universal color filter faces a cut-rank barrier: for prefixes listing the h-element subsets A, and suffixes listing complements of h-element subsets B, the exact-requirement matrix is the identity, with h=floor(k/2). Any common linear state across the cut has dimension at least binom(k,h). This argument concerns arbitrary shared filters, and leaves room for circuit-specific state, other decompositions or nonlinear summaries.

## An actual field matrix and a fixed public sink form

Use the given topological gate order. At first use branch once on each primary value with respective weights 1 and t_i; unused primaries branch and immediately merge. Keep each live wire until its last use. At each gate form the deterministic NAND transition, dropping expired wires. Include all assignments to the current live set whether reachable or not. The final accept state has a unit arc to a separate sink. There is exactly one source-to-sink path per accepting primary assignment, with its monomial weight. For arbitrary individual rainbow edge weights, multiply the chosen cycle-orientation edge product once per wire when its value is determined, and the unique local slot edge product once per gate/unary constraint; all products are local to determined values. This constructs the same target coefficient, though the degree-n estimate specifically uses only the primary weights.

Let B be the strictly upper-triangular weighted adjacency matrix including parallel edges additively, T=I-B, and M be T with the sink row and source column deleted. T^-1=I+B+... so v=T^-1 e_sink has v_sink=1 and v_source=P(t). If P=0 then deleting the zero source coordinate gives a kernel vector of M with sink coordinate 1. Conversely if M has a kernel vector, extend it by 0 at the source. Its image under T is supported only at the sink. Invertibility of T forces that vector to be a multiple of v. Thus M has nullity exactly one when P=0, otherwise zero. The cofactor formula gives det(M)=±P. For fixed weights sample u independently uniformly in K^(N-1), insert 0 at its source, and publish (Mu,beta+u_sink) and all primary weights. On NO the kernel translation works for every weight choice and every independent repetition, giving perfect full-view equality. A stronger structural fact than generic singularity makes the same public h=e_sink work for all NO matrices.

On a bank where P is nonzero, extend y=Mu by 0 at the sink and compute z=T^-1(y,0) by a backward DAG traversal. The actual extension of u is z+lambda v with source coordinate 0, forcing lambda=-z_source/P. As z_sink=0, lambda is the masked u_sink. Compute P via a second backward traversal, try the next independent bank if zero. The issuer needs no path-sum, judgment of reachability or SAT test. The decoder does compute the field path sum, independently of its witness, so this is efficient only with a small actual representation. A succinct description of an exponentially large layer gives no efficient registered decoder. Lean checks the bordered-block kernel direction and decoded scalar identity separately. The entire compiler and runtime are functional evidence via the Python replay, not Lean Machine theorems.

The compiler uses N=2+sum_events 2^(new live width), including the initial source and final sink. Each transition needs at most one field multiply and add for the sparse product; each vertex needs O(1) extra operations. Building destinations from bit positions directly also costs up to O(width) index work per transition, in addition to scheduling, field/binary encoding and tape access. Our 4096-gate Fibonacci-style fixture uses width 2, N=16,516 and 16,643 transitions. A single full transcript is (N+128)*16=266,304 raw bits, of which 264,256 are products and tag; fifteen banks cost 3,994,560 raw bits. Each bank consumes (N-1+128)*16 independent fair bits. Register framing, machine description, tape movement, verified native clocks and full capped-object scores remain open. The ordinary generic scheme at r=9 would incur at most q^-9=2^-144 per singular bank and less than 2^-140 across fifteen; the sink scheme has zero NO gap even with one form. The raw breadth-first tree of 2048 repeated NAND leaves, eleven binary levels and a final negation has scheduled width 2048 and N of bit length 2051. It admits semantic simplification and does not prove an intrinsic lower bound.

A deterministic modular alternative uses this DAG with unweighted integer edges and multiplicities so its path count lies in [0,2^128]. Distinct primes whose product exceeds 2^128 cannot all divide a positive count. Ten distinct 16-bit primes are sufficient; at least one bank decodes on every YES, all banks have fixed sink coupling on NO. This argument needs a nonnegative integer witness count or consistent signs, not arbitrary signed count cancellation. An individual prime may divide a positive count (e.g. two witnesses in characteristic two); independent randomized weights avoid this formal cancellation with the error above. Fair sampling in odd fields can use bounded rejection, publishing a payload-independent failure symbol and budgeting its probability. The binary-field construction uses fixed exact fair tapes.

## Reproducible checks

Removing this Markdown fence yields a self-contained Python 3 replay. The complete distribution counters and explicit perfect-match enumeration are intentionally independent of the algebraic formulas. The last size bound enumerates only layer widths. The whole-key decoder and translation checks are performed on actual matrices represented by sparse adjacency, for small instances and the narrow full-sized positive case.

```python
from itertools import permutations, product
from collections import Counter
from random import Random
from fractions import Fraction

PORT=(((0,),(1,)),((0,1),(2,)),((0,),(1,2)))
def norm(n,g):
    return [(a if a<=n+i else 0,b if b<=n+i else 0) for i,(a,b) in enumerate(g)]
def values(n,g,x):
    v=[1]+[(x>>i)&1 for i in range(n)]
    for a,b in norm(n,g):v.append(1-v[a]*v[b])
    return v

def rainbow(n,g):
    g=norm(n,g)
    occ=[]; rules=[]
    def append(wires,sets):
        base=len(occ);occ.extend(wires)
        rules.append((list(range(base,len(occ))),sets))
    for i,(a,b) in enumerate(g):append([a,b,n+1+i],PORT)
    for x in range(1,n+1):append([x],(((0,),(0,)),))
    for x in (0,n+len(g)):append([x],(((),(0,)),))
    l=len(occ); edges=[[] for _ in range(2*l)]; by={}
    for i,x in enumerate(occ):by.setdefault(x,[]).append(i)
    for idx in by.values():
        for j,i in enumerate(idx):
            edges[i]+=[(i,2*i+1),(idx[(j+1)%len(idx)],2*i)]
    for idx,t in rules:
        for k,i in enumerate(idx):
            for b in range(2):
                for s in t[k][b]:edges[l+idx[s]].append((l+idx[s],2*i+b))
    return occ,rules,by,edges
def convert(x,n,g,desc):
    occ,rules,by,edges=desc
    v=values(n,g,x); l=len(occ)
    if not v[-1]:return None
    chosen=[None]*(2*l)
    for idx in by.values():
        for i in idx:chosen[i]=edges[i][v[occ[i]]]
    for idx,t in rules:
        cats=[v[occ[i]] for i in idx]
        ps=[p for p in permutations(range(len(idx))) if all(p[k] in t[k][b] for k,b in enumerate(cats))]
        assert len(ps)==1
        for k,s in enumerate(ps[0]):
            row=l+idx[s]
            chosen[row]=(row,2*idx[k]+cats[k])
    assert all(e in es for e,es in zip(chosen,edges))
    assert len({e[0] for e in chosen})==len({e[1] for e in chosen})==2*l
    return tuple(chosen)
def brute_rainbow(edges):
    seq=sorted(range(len(edges)),key=lambda z:len(edges[z]))
    def visit(j,r,c):
        if j==len(seq):return 1
        ans=0
        for y,k in edges[seq[j]]:
            if not (r>>y&1 or c>>k&1):ans+=visit(j+1,r|(1<<y),c|(1<<k))
        return ans
    return visit(0,0,0)

Q=1<<16
MOD=0x1100b
def mul(a,b):
    if a in (0,1):return b if a else 0
    if b in (0,1):return a if b else 0
    c=0
    while b:
        if b&1:c^=a
        b>>=1;a<<=1
        if a&Q:a^=MOD
    return c
def pm(x,y):
    while x.bit_length()>=y.bit_length():x^=y<<(x.bit_length()-y.bit_length())
    return x
def gcd(x,y):
    while y:x,y=y,pm(x,y)
    return x
def power(a,n):
    b=1
    while n:
        if n&1:b=mul(a,b)
        a=mul(a,a);n>>=1
    return b
assert power(2,1<<16)==2 and gcd(power(2,1<<8)^2,MOD)==1

def make(n,g,t,build=True):
    # The live sets are determined without circuit-value propagation.
    g=norm(n,g);last={};first={}
    for i,(a,b) in enumerate(g):
        for x in (a,b):
            if x:
                last[x]=i
                if x<=n:first.setdefault(x,i)
    last[n+len(g)]=len(g)
    events=[('input',x,-1) for x in range(1,n+1) if x not in first]
    for i,(a,b) in enumerate(g):
        events.extend(('input',x,i) for x in sorted({a,b}) if first.get(x)==i)
        events.append(('gate',n+1+i,i))
    live=[];layers=1;peak=0;adj=[[]] if build else None;start=0
    for typ,x,i in events:
        if typ=='input':new=live+([x] if x in first else [])
        else:new=[v for v in live if last[v]>i]+([x] if last.get(x,-1)>i else [])
        oldsz=1<<len(live);newsz=1<<len(new);tail=start+oldsz
        if build:
            adj.extend([] for _ in range(newsz))
            for j in range(oldsz):
                bits={s:(j>>k)&1 for k,s in enumerate(live)};bits[0]=1
                if typ=='input':vals=((0,1),(1,t[x-1]))
                else:
                    a,b=g[i];vals=((1-bits[a]*bits[b],1),)
                for val,weight in vals:
                    bits[x]=val
                    dst=sum(bits[s]<<k for k,s in enumerate(new))
                    adj[start+j].append((tail+dst,weight))
        layers+=newsz;peak=max(peak,len(new));live=new;start=tail
    assert live==[n+len(g)]
    if build:
        adj[start+1].append((layers,1));adj.append([])
    return peak,layers+1,adj
def pathvec(adj):
    v=[0]*len(adj);v[-1]=1
    for i in reversed(range(len(v)-1)):
        for j,a in adj[i]:v[i]^=mul(a,v[j])
    return v
def encrypt(adj,beta,u):
    # u[0]=0 by convention; it is not sampled or sent.
    y=[]
    for i,row in enumerate(adj[:-1]):
        z=u[i]
        for j,a in row:z^=mul(a,u[j])
        y.append(z)
    return y,beta^u[-1]
def decrypt(adj,y,t):
    c=[0]*len(adj)
    for i in reversed(range(len(adj)-1)):
        c[i]=y[i]
        for j,a in adj[i]:c[i]^=mul(a,c[j])
    s=pathvec(adj)[0]
    return None if not s else t^mul(c[0],power(s,Q-2))

def exact_generic():
    # F2, M=diag(1,0). Include all h vectors in the transcript.
    for r in (1,2,3):
        H=[Counter(),Counter()]
        for hu in product(range(4),repeat=2*r):
            hs=hu[:r];us=hu[r:];v=tuple(u&1 for u in us)
            t=sum((h&u).bit_count() for h,u in zip(hs,us))&1
            for b in range(2):H[b][hs,v,t^b]+=1
        tv=Fraction(sum(abs(H[0][k]-H[1][k]) for k in H[0].keys()|H[1].keys()),2*sum(H[0].values()))
        assert tv==Fraction(1,2**r)
        print("entire random-form law",r,tv)

rng=Random(262)
exact_generic()
for n,g in ((1,[(1,1)]),(1,[(4,1),(2,2)]),(2,[(1,2),(2,3)]),(2,[(0,0),(3,3)]),
            (2,[(0,0)])):
    desc=rainbow(n,g)
    valid=[x for x in range(1<<n) if convert(x,n,g,desc) is not None]
    assert len(valid)==brute_rainbow(desc[-1])
    for _ in range(12):
        ts=[rng.randrange(Q) for _ in range(n)]
        peak,N,adj=make(n,g,ts)
        target=0
        for x in valid:
            w=1
            for i,t in enumerate(ts):
                if x>>i&1:w=mul(w,t)
            target^=w
        v=pathvec(adj);assert v[0]==target and v[-1]==1
        u=[0]+[rng.randrange(Q) for _ in range(N-1)]
        for b in (0,1):
            y,mask=encrypt(adj,b,u)
            if target:assert decrypt(adj,y,mask)==b
            else:assert encrypt(adj,b^1,[a^t for a,t in zip(u,v)])==(y,mask)
print("small bijections, polynomials and whole-key tests passed")

g=[(1,2),(129,1)]
for j in range(2,4096):g.append((128+j,127+j))
desc=rainbow(128,g)
print("registered colors, edges",len(desc[-1]),sum(map(len,desc[-1])))
assert len(desc[-1])==24836 and sum(map(len,desc[-1]))==57862
for x in range(4):assert (convert(x,128,g,desc) is not None)==bool(values(128,g,x)[-1])
ts=[rng.randrange(2,Q) for _ in range(128)]
peak,N,adj=make(128,g,ts)
u=[0]+[rng.randrange(Q) for _ in range(N-1)]
for b in (0,1):
    yy,zz=encrypt(adj,b,u)
    assert decrypt(adj,yy,zz)==b
print("registered width, vertices, transitions, one-bank bits",peak,N,sum(map(len,adj)),16*N)
g=[(1,1)]*2048
layer=list(range(129,129+2048))
while len(layer)>1:
    new=[]
    for a,b in zip(layer[::2],layer[1::2]):
        g.append((a,b));new.append(128+len(g))
    layer=new
g.append((layer[0],layer[0]))
w,N,_=make(128,g,[1]*128,False)
print("live scheduled width and size bit length",w,N.bit_length())

```
