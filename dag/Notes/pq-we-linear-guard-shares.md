---
title: Binary share synthesis and two-certificate recovery for witness encryption
refs: [definition:WE_CircuitSAT, theorem:AdvancedEncryption.WE.Span.mask_fiber, theorem:AdvancedEncryption.WE.Span.pair_flip_packing]
tags: [witness-encryption, linear-secret-sharing, complexity, compilation]
---

[PR 103](https://github.com/MachinaIO/SigabaPark/pull/103) identifies local predicates with witness translators and compiles the resulting monotone access condition into an AND/OR tree. There is another way to transmit correlated bits under these predicates. Give each predicate a collection of binary linear forms, encrypt one bit per form under that predicate, and recover the message by XORing a certified subset of the available forms. The access matrix is generated from the public statement. This note gives a bounded compiler, a weighted two-certificate specialization and a comparison to encrypting a whole NAND verifier. All constructions inherit the security assumption of the leaf WE. The sharing and compilation need no PRG or public correction bits.

Monotone span programs, linear secret sharing, matroid-port constructions and the prefix-code connection for two-threshold sharing are established tools. The contributions here are a blocker-based synthesis and validation procedure for the WE compiler, the use of actual predicate-encryption costs as weights, an interval optimization, and separate Enc and Dec accounting. See [linear secret sharing for matroid ports](https://www.kybernetika.cz/content/2020/5/903) and [Komargodski, Naor and Yogev on prefix codes](https://eprint.iacr.org/2016/194.pdf).

### Synthesizing binary linear forms

The input is a complete antichain of minimal authorized label sets obtained by a witness-preserving compiler. Alternatively, use a publicly checked outer monotone circuit on guards with disjoint private input blocks: satisfiable local predicates can then be realized simultaneously. A witness for the original statement supplies a certificate for every guard evaluating to one. Overlapping private inputs without a gluing proof are unsound, since x and its negation can each have separate witnesses. Route constant predicates directly.

Enumerate the minimal hitting sets B of the authorized antichain, with a work cap. The complement of each B is maximal unauthorized. Use one binary coordinate per B, and let the secret form T be the all-ones vector. For label i let S_i be the set of coordinates B containing i. Issue only rows supported inside S_i under that label. For every false instance, the set of all satisfiable labels misses some hitting set B. All rows available there are zero in coordinate B; toggling that coordinate flips the secret and fixes them all.

Initially propose one row equal to the indicator of S_i for each nonempty S_i. For a minimal authorized set M, try to span T using its rows. The supports of the rows need an odd cover of each blocker coordinate. Ordinary coverage alone only guarantees that the union of the S_i for i in M is the full coordinate set. If the parity test fails, choose a subset J of M allowed to receive additional rows. Let U be the union of its S_i. Solve the linear system on coordinates outside U using the existing M rows. When solvable, the residual is supported on U. Partition its nonzero coordinates among labels i in J that cover them, adding at most one row per such label. Adding rows inside these permitted supports preserves every unauthorized masking direction. Taking J=M always succeeds. Search small subsets within a budget and then try M. Finally try deleting rows while preserving every affected minimal authorized set. Independently recheck every minimal authorized span and the no-leak coordinate invariant for every blocker. Bounds on state count, emitted rows, bit-vector lengths and compiler work are required before allocation. Partial enumeration of blockers cannot certify privacy. On budget exhaustion keep a complete preexisting formula or whole-circuit plan.

Choose a basis of the row forms and T, with T first. If its dimension is r, set the first evaluation bit to the message and sample the other r-1 bits uniformly. Linear independence makes this identical to evaluating all original forms on a uniform coordinate vector conditioned on T. Dec solves for T using rows whose labels have a local certificate, then opens just the selected rows and XORs them. All matrices and reconstruction coefficients are public functions of the statement and the available certificate labels. For a fixed false statement the coordinate toggle couples encryptions of both messages, changing only payloads under false labels. Hybridize those occurrences using fresh leaf coins; charge simulation cost, nonuniform choice of blocker if used, and the sum of false-leaf advantages. A reversed bit challenge can be handled by complementing the distinguisher output. The Lean fiber theorem gives an exact equality of counts for each visible transcript under a linear secret-changing shift. The argument handles quantum postprocessing of the classical data if the leaf proof does. Correctness error for a supplied witness is at most the sum of errors of its selected decryptions.

In 120 random small policies, 26 needed repairs. Every one of 4292 label-availability patterns agreed with the target; the test also compares entire unauthorized transcript distributions for compact ranks at most nine. As a structured control take all nonzero vectors of a binary vector space except the target and authorize a set when it spans the target. Feed only its minimal sets to the synthesizer. In dimension three it returned six leaf encryptions and two sharing coins, versus twelve leaves from the bounded formula compiler of PR 103. In dimension four it returned fourteen encryptions and three coins, versus 322 leaves from that bounded compiler on the 91-minterm input. Every label is essential in these examples; one bit per label is sufficient and no essential label can be omitted from an occurrence-labeled sharing scheme. These are known ideal access structures. The formula counts are reproducible outputs, not lower bounds. The raw incidence heuristic requires repairs for two-threshold profiles and by itself gave 35 leaves for eight participants.

### Two certificates from different classes

Given a structurally verified monotone outer circuit, reject the specialized mode if any singleton or the empty input is authorized. For each vertex i compute the set of vertices not forming an authorized pair with i, including itself. Check that these sets partition the vertices into at least two classes and that the full set of each class is unauthorized. All cross-class pairs are authorized by construction. Monotonicity then proves exact agreement on every subset: either it contains a cross-class pair or lies in one rejected class. This costs polynomially many evaluations and does not enumerate all subsets. The listing verifies a supplied cut of a NAND netlist by traversing signed wires in the output cone, requiring positive occurrences of the designated guard ports, and checking that their private primary-input supports are disjoint. Normalize unavailable reads to true. A production compiler must bound the search for a cut; a failed candidate leaves the existing backend available.

Give each class a distinct prefix-free binary word. Sample independent uniform r_j for code positions up to the maximum length. A guard i with class word c is given one WE encryption of r_j xor (c_j times b) per position j of c. Two certified guards in different classes open just the two ciphertexts at their first differing position. XOR yields b. For a false statement all satisfiable guards belong to one class, so switching b and translating r_j by that class's bit at position j preserves all of their shares. If no guard is satisfiable use any mask translation. Again only false leaf ciphertexts need a computational hybrid. When several guards of a single class have witnesses they all expose the same masked values at that class; encryption coins for their separate ciphertexts are independent. An erroneous leaf decryption costs at most twice the maximum per-leaf error along a valid pair.

Within the fixed per-type bit-encryption interface, assign a positive weight to each guard (e.g. residues per one-bit local WE). Huffman-code the classes with weight equal to the sum of weights of their members. This minimizes the sum of weights times code lengths among prefix layouts. For two-of-n with singleton classes this is also optimal among perfect **binary linear** sharing layouts with that fixed per-bit weighting. To see the restriction, condition on a unit change of the secret in the linear sharing randomness. For party i its mask-preserving directions are a nonempty affine set by single-party privacy. If i receives l_i linear bits, this set occupies at least a 2^-l_i fraction of all unit-secret directions (at most l_i independent equations). Two such sets cannot intersect because any two parties reconstruct the secret. Hence sum_i 2^-l_i <= 1. Kraft's inequality permits a prefix code of these lengths, and weighted prefix optimality applies. The second Lean theorem verifies the disjoint-fiber counting step. This optimum excludes encodings of composite guard predicates and other cryptographic backends. For equal weight at n=8 and n=128 the counts are respectively 24 and 896 one-bit encryptions, with two selected decryptions in both cases.

### Trading local sampling cost for shorter ciphertexts

For the singleton-class threshold, allow a contiguous group of guards to be treated as one composite local statement requiring at least one or at least two guards. Build each macro by extracting its guard cones, renaming their private inputs and appending the threshold test; project an original witness onto its canonical predicate ports. Let C1(I) and C2(I) be the minimum additive encryption cost for these two conditions on interval I within the following family. The cost for two on a singleton is zero because the condition is impossible. For one, either choose the direct macro or split I=L,R and encrypt the same bit independently under both C1 plans. For two, use the direct macro or the sum of four costs C2(L)+C2(R)+C1(L)+C1(R). In the split, both internal two-threshold ciphertexts carry b. The two one-threshold ciphertexts carry independent XOR shares r and r xor b. A valid pair in one child uses that child's two-threshold plan; one in each child uses both one-threshold plans. If fewer than two guards are satisfiable, both internal two-threshold statements are false and at least one side of the cross pair is false. This gives the usual AND and OR hybrid reductions. Leaf randomness and each split's share coins are fresh. Compute the interval DP in cubic time in the number of guards plus the cost of constructing the bounded macro estimates. Count selected Dec work by taking the maximum of the two internal plans' ceilings and the sum of the cross plans' ceilings. Counting work for a witness does not require searching all pairs. The listing compares ciphertext-optimized and sampled-column-optimized interval plans for one fixed ordering. A complete selector also compares the weighted prefix option and the monolithic baseline, charging compilation and public layout reconstruction. These algorithms and their polynomially capped fallbacks preserve polynomial bounds for ciphertext length, Enc and Dec when the leaf backend has them.

The test circuit has 128 private inputs, 16 unequal eight-input guards, and 4096 raw NAND gates. The outer computation checks for at least two successful guards. It is a resource-accounting control; the guards are small enough to solve publicly. Use the shortened matrix backend of [PR 99](https://github.com/MachinaIO/SigabaPark/pull/99), with the same scale m=128w and 16 terminal columns on every compiled guard and on the whole circuit. This fixes geometry for comparison and supplies no concrete hardness estimate. For h>=2 levels count 2m(1+16)+2(h-2)m² serialized residues, 2((h-2)m+16) sampled preimage columns, and (h-2)m²+16m selected modular multiply-adds per single matrix-chain call. Include both endpoints. The estimates omit framing, the public compiler, trace generation, sampling work per column, and sequential scans.

| Layout | Matrix residues | Preimage columns | Selected modular multiply-adds, worst-pair upper bound |
| --- | ---: | ---: | ---: |
| Whole circuit, h=976 and w=189 | 1140073401600 | 47126048 | 570036676608 |
| Equal-depth prefix | 1015864459264 | 79874048 | 51056791552 |
| Ciphertext-weighted prefix | 819335028992 | 74221024 | 51056791552 |
| Ciphertext-optimized interval | 723424925440 | 58593824 | 119217580032 |

At equal scale the interval plan saves 36.55% of the monolithic matrix payload and 79.09% of the selected multiply-add ceiling, while increasing sampled columns by 24.33%. Minimizing sampled columns in the interval family selects the whole circuit. The weighted prefix saves 19.35% of residues over the equal-depth prefix and has the lowest Dec ceiling in the table. Choose the objective using the backend's actual costs. The three algorithms are polynomial, but the table establishes no wall-clock speedup and no general WE proof under the registered PQ assumptions. The pair-policy recognizer is independently tested on all four-input monotone truth tables and the weighted optimizer against exact small tree costs. The control also replays actual NAND witnesses onto the selected guards and macros.

### What a shorter preimage column costs inside Enc

Counting columns alone treats every matrix as having the same dimension. For a dense reverse nearest-plane sampler with an already triangularized basis, one column of dimension m draws m one-dimensional Gaussian coefficients. Its triangular center update uses exactly m(m-1)/2 multiply-subtracts if each iteration updates only the still-unprocessed coordinates. Thus a leaf with P sampled columns contributes Pm scalar draws and Pm(m-1)/2 center updates. This models a specific sampler and excludes basis construction, finite-precision arithmetic costs, proposal iterations inside a scalar draw, matrix target preparation and final coefficient conversion.

In the same control, the monolithic setup requires 1140073353216 scalar draws and 13789757243824128 center updates. The payload-optimized interval plan requires 723424145408 draws and 5112778832201728 updates. It therefore improves these two Enc operation counts even though it samples more, shorter columns. Optimizing center updates instead chooses a different layout with 5002750890530816 updates, 772234497280 transmitted residues and a Dec ceiling of 86410954752 multiply-adds. The listing replays the emitted macro calls to verify additive counts and exhausts all 120 distinct pairs to check the maximum selected cost.

The payload-optimized layout continues to improve the three metrics over a range of common scalings. Keep the chosen tree fixed. If m=a w on every macro, a>=1 is integral and 1<=t<=12a, its smallest width can support t columns. Put A=sum (h-2)w² over emitted macros and let z=12. Full residue count is at most 2a²[A+(z+1)sum w]. Scalar draws are at most 2a²[A+z sum w]. Center updates are at most a³ sum[((h-2)w+z)w²]. For the whole shape H=976,W=189 the respective lower bounds are 2a²(H-2)W², 2a²(H-2)W², and a³(H-2)W²(W-1). For Dec use a² times the sum of (h-2)w²+zw on the selected calls, maximizing over pairs, versus at least a²(H-2)W². An accepting witness with more guards can select exactly two of them before routing. The verified upper/lower coefficient pairs are (22116383,34792254) for payload, (22113336,34792254) for scalar draws, (2440641946,6540943752) for triangular updates, and (7278138,34792254) for Dec. These establish at least 35%, 35%, 60% and 78% savings respectively in these counts for the stated common-scale range. A cryptographic instantiation still has to meet the noise, reduction, precision and correctness requirements and charge all omitted work.

For reproduction use Python. Save the listings as cover.py, pair.py and intervals.py. Take labels.py and shapes.py from [PR 103 at 45c9fbb](https://github.com/MachinaIO/SigabaPark/blob/45c9fbbfb4f725c3301522f95ca881d3daa8568c/dag/Notes/pq-we-reusable-local-witnesses.md), nand.py from [PR 102 at d49bd9e](https://github.com/MachinaIO/SigabaPark/blob/d49bd9eeb7d5a4cacdfd6b4d774348e55ad6a0f9/dag/Notes/pq-we-separator-paths.md), and frontend.py from [PR 99 at 58036ab](https://github.com/MachinaIO/SigabaPark/blob/58036abbee86216e6e0bf18a4a8234c6d55d82cb/dag/Notes/pq-we-live-clause-matrix-product.md). Run python cover.py labels.py and python pair.py nand.py labels.py shapes.py frontend.py intervals.py.

~~~python
"""Bounded binary span-program synthesis on the logical conditions of PR 103."""
from itertools import combinations, product
from random import Random

class OverBudget(Exception): pass
class Meter:
    def __init__(self,n):self.left=n
    def tick(self,n=1):
        self.left-=n
        if self.left<0:raise OverBudget

def bits(x):
    while x:
        b=x&-x;yield b.bit_length()-1;x-=b

def echelon(rows):
    b={}
    for j,v in enumerate(rows):
        coeff=1<<j
        while v:
            i=v.bit_length()-1
            if i not in b:b[i]=(v,coeff);break
            a,c=b[i];v^=a;coeff^=c
    return b

def solve(b,target):
    coeff=0
    while target:
        i=target.bit_length()-1
        if i not in b:return None
        v,c=b[i];target^=v;coeff^=c
    return coeff

def dot(x,y):return (x&y).bit_count()%2
def selected(rows,m):return [(i,v) for i,v in rows if m>>i&1]
def supported(rows,m,target):return solve(echelon(v for i,v in selected(rows,m)),target) is not None

def minimal(family):
    ans=[]
    for a in sorted(set(family),key=lambda x:(x.bit_count(),x)):
        if not any(a&b==b for b in ans):ans.append(a)
    return tuple(ans)

def transversals(terms,meter):
    cur=(0,)
    for t in terms:
        nxt=[]
        for x in cur:
            meter.tick()
            add=[x] if x&t else [x|(1<<j) for j in bits(t)]
            for a in add:
                meter.tick(1+2*len(nxt))
                if not any(a&b==b for b in nxt):
                    nxt=[b for b in nxt if b&a!=a]+[a]
        cur=tuple(nxt)
    return cur

def repair(terms,block,d,meter,order=None):
    target=(1<<len(block))-1
    S=[sum(1<<j for j,b in enumerate(block) if b>>i&1) for i in range(d)]
    rows=[(i,v) for i,v in enumerate(S) if v]
    added=0
    for m in (terms if order is None else order):
        meter.tick()
        active=[v for _,v in selected(rows,m)]
        if solve(echelon(active),target) is not None:continue
        available=list(bits(m))
        def try_subset(T):
            meter.tick()
            union=0
            for i in T:union|=S[i]
            outside=target^union
            c=solve(echelon(v&outside for v in active),outside)
            if c is None:return False
            residual=target
            for j in bits(c):residual^=active[j]
            for i in T:
                piece=residual&S[i]
                if piece:rows.append((i,piece));residual^=piece
            assert residual==0
            return True
        # Full support always works. Bound attempts per minterm independently.
        done=False;attempt=0
        for l in range(1,len(available)):
            for T in combinations(available,l):
                attempt+=1
                if try_subset(T):done=True;break
                if attempt>=64:break
            if done or attempt>=64:break
        if not done:assert try_subset(available)
        added+=1
    for j in reversed(range(len(rows))):
        i,_=rows[j];other=rows[:j]+rows[j+1:]
        for m in terms:
            if m>>i&1:
                meter.tick()
                if not supported(other,m,target):break
        else:rows=other
    # Recheck every minimal YES and every maximal NO before emitting a plan.
    for m in terms:
        meter.tick()
        if not supported(rows,m,target):raise ValueError('failed YES certificate')
    for j,b in enumerate(block):
        meter.tick()
        if any((v>>j&1) and not (b>>i&1) for i,v in rows):raise ValueError('failed NO certificate')
    return target,rows,added

def compile_plan(terms,d,cap):
    if not terms or 0 in terms:raise ValueError('route constants directly')
    meter=Meter(cap)
    block=transversals(terms,meter)
    target,rows,added=repair(terms,block,d,meter)
    # Choose target first in an independent basis of all linear forms.
    basis=[target];span=echelon(basis)
    for _,v in rows:
        if solve(span,v) is None:basis.append(v);span=echelon(basis)
    packed=[(i,solve(span,v)) for i,v in rows]
    return packed,len(basis),added,len(block)

def encrypt(plan,b,coin,enc):
    rows,r,_,_=plan;z=(coin(r-1)<<1)|b
    return [enc(i,dot(v,z)) for i,v in rows]
def decrypt(plan,ct,cert,dec):
    rows=plan[0];idx=[j for j,(i,v) in enumerate(rows) if i in cert]
    c=solve(echelon(rows[j][1] for j in idx),1)
    if c is None:return None
    out=0
    for k in bits(c):
        j=idx[k];i=rows[j][0];v=dec(i,ct[j],cert[i])
        if v is None:return None
        out^=v
    return out

def run(labels):
    rng=Random(711);checks=failed=0
    for _ in range(120):
        d=rng.randrange(2,8);terms=minimal([rng.randrange(1,1<<d) for j in range(rng.randrange(1,14))])
        p=compile_plan(terms,d,100000);rows,r,reps,bs=p;failed+=reps>0
        for live in range(1<<d):
            yes=any(m&live==m for m in terms)
            assert supported(rows,live,1)==yes
            if r<=9 and not yes:
                # Complete visible transcripts for fixed formal availability.
                obs=lambda z:tuple(dot(v,z) for i,v in rows if live>>i&1)
                assert sorted(obs(z) for z in range(0,1<<r,2))==sorted(obs(z) for z in range(1,1<<r,2))
            for b in (0,1):
                ct=encrypt(p,b,rng.getrandbits,lambda i,v:v if live>>i&1 else 0)
                out=decrypt(p,ct,{i:i for i in bits(live)},lambda i,c,w:c)
                assert out==(b if yes else None)
            checks+=1
    print('label availability patterns / random policies needing repair',checks,failed)
    for r in (3,4):
        vec=list(range(2,1<<r));d=len(vec)
        terms=minimal([m for m in range(1,1<<d) if solve(echelon(vec[j] for j in bits(m)),1) is not None])
        p=compile_plan(terms,d,1000000)
        f=labels['circuit'](terms,labels['Limit'](100000))
        print('binary vector example: rank,kinds,minterms,formula leaves,new leaves,sharing bits,repair,blockers',
              r,d,len(terms),labels['size'](f),len(p[0]),p[1]-1,p[2],p[3])
    for d in (3,5,8):
        terms=tuple((1<<i)|(1<<j) for i,j in combinations(range(d),2))
        p=compile_plan(terms,d,100000)
        print('2-of-n: n,formula leaves,new leaves,repair',d,labels['size'](labels['circuit'](terms,labels['Limit'](100000))),len(p[0]),p[2])
if __name__=='__main__':
    import runpy,sys
    run(runpy.run_path(sys.argv[1]))
~~~

~~~python
"""Recognize complete multipartite two-certificate policies and compile weighted shares."""
from heapq import heappush,heappop
from itertools import combinations,product
from random import Random

def parts(d,monotone):
    # Precondition: the supplied function is monotone. NAND caller verifies the cone.
    if d<2 or monotone(0) or any(monotone(1<<i) for i in range(d)):return None
    masks=[]
    for i in range(d):
        masks.append(sum(1<<j for j in range(d) if j==i or not monotone((1<<i)|(1<<j))))
    groups=sorted(set(masks))
    if len(groups)<2:return None
    for i,mask in enumerate(masks):
        if any(masks[j]!=mask for j in range(d) if mask>>j&1):return None
    if any(monotone(mask) for mask in groups):return None
    return [[i for i in range(d) if mask>>i&1] for mask in groups]

def codes(groups,weights):
    heap=[];tag=0
    for group in groups:
        heappush(heap,(sum(weights[i] for i in group),tag,tuple(group),None));tag+=1
    while len(heap)>1:
        x=heappop(heap);y=heappop(heap)
        heappush(heap,(x[0]+y[0],tag,None,(x,y)));tag+=1
    result={};stack=[(heappop(heap),())]
    while stack:
        node,c=stack.pop()
        if node[2] is not None:
            for i in node[2]:result[i]=c
        else:
            for bit,child in enumerate(node[3]):stack.append((child,c+(bit,)))
    return result

def encrypt(code,b,randbit,enc):
    r=[randbit() for _ in range(max(map(len,code.values())))]
    return {i:[enc(i,r[j]^(b*x)) for j,x in enumerate(word)] for i,word in code.items()}
def decrypt(code,ct,certs,dec):
    if not certs:return None
    i=next(iter(certs))
    for k in certs:
        for j,(x,y) in enumerate(zip(code[i],code[k])):
            if x!=y:
                a=dec(i,ct[i][j],certs[i]);b=dec(k,ct[k][j],certs[k])
                return a^b if a is not None and b is not None else None
    return None

def cone(n,gates,guards):
    # A signed port beneath NAND is either supplied positively or this layout is rejected.
    if len(set(guards))!=len(guards) or any(not (1<=x<=n+len(gates)) for x in guards):
        raise ValueError('invalid or duplicate guard wires')
    gates=[tuple(x if 0<x<n+i+1 else 0 for x in gate) for i,gate in enumerate(gates)]
    guardid={x:i for i,x in enumerate(guards)}
    out=n+len(gates) if gates else 0
    seen=set();todo=[(out,True)]
    while todo:
        x,pos=todo.pop()
        if (x,pos) in seen:continue
        seen.add((x,pos))
        if x in guardid:
            if not pos:raise ValueError('negative guard port')
        elif x:
            if x<=n:raise ValueError('uncovered outer input')
            todo.extend((a,not pos) for a in gates[x-n-1])
    def f(mask):
        d={0:1}
        for x in sorted({x for x,pos in seen}-{0}):
            if x in guardid:d[x]=mask>>guardid[x]&1
            else:
                a,b=gates[x-n-1];d[x]=1-d[a]*d[b]
        return bool(d[out])
    # Verify private primary-input supports are disjoint.
    used=set()
    for x in guards:
        private=set();local=set();todo=[x]
        while todo:
            y=todo.pop()
            if y in local:continue
            local.add(y)
            if 1<=y<=n:private.add(y)
            elif y>n:todo.extend(gates[y-n-1])
        if used&private:raise ValueError('overlapping private inputs')
        used|=private
    return f

def controls(nand,labels,shapes,front,planner=None):
    rng=Random(707)
    n=128;g=[];guards=[];keys=[];wm=[]
    def N(a,b):g.append((a,b));return n+len(g)
    def neg(a):return N(a,a)
    def both(a,b):return neg(N(a,b))
    def either(a,b):return N(neg(a),neg(b))
    for i in range(16):
        offset=len(g);xs=[8*i+k+1 for k in range(8)];negx=list(map(neg,xs));cur=0
        for _ in range(3+2*i):
            a,b,c=rng.sample(range(8),3)
            cur=both(cur,either(either(xs[a],(xs,negx)[rng.randrange(2)][b]),negx[c]))
        guards.append(cur)
        # Rebase the guard onto eight local wires for the matrix-size comparison.
        ren={0:0,**{x:j+1 for j,x in enumerate(xs)}};sg=[]
        for j,(a,b) in enumerate(g[offset:]):
            sg.append((ren[a],ren[b]));ren[n+offset+j+1]=8+j+1
        p=nand['schedule'](8,sg,[0,len(sg)])
        k,ports=labels['canonical'](p,8,0,0,0)
        wm.append(tuple(p[3][0][j]-1 for j in ports))
        keys.append(k)
    # The outer threshold recurrence, expressed as a circuit with shared wires.
    one=neg(0);two=one
    for port in guards:
        two=either(two,both(one,port));one=either(one,port)
    gap=4096-len(g);assert gap>=2
    if gap%2:N(0,0)
    for _ in range(gap//2):two=neg(neg(two))
    f=cone(n,g,guards);groups=parts(len(guards),f);assert len(groups)==16
    hws=[shapes['matrix_shape'](k,front['compile_program']) for k in keys]
    def counts(hw,alpha,t):
        h,w=hw;m=alpha*w
        return (2*m*(1+t)+2*(h-2)*m*m,2*((h-2)*m+t),(h-2)*m*m+m*t)
    leaf=[counts(hw,128,16) for hw in hws]
    code=codes(groups,[c[0] for c in leaf]);uniform=codes(groups,[1]*16)
    def total(code,j):return sum(len(code[i])*leaf[i][j] for i in code)
    print('4096 NANDs, bytes proxy in residues / sampled columns, equal vs weighted:',
          total(uniform,0),total(code,0),total(uniform,1),total(code,1))
    whole=nand['schedule'](n,g,[0,len(g)]);key,_=labels['canonical'](whole,n,0,0,0)
    whole_hw=shapes['matrix_shape'](key,front['compile_program']);mon=counts(whole_hw,128,16)
    print('whole shape / residues / sampled columns / Dec MACs vs worst selected pair MACs:',whole_hw,*mon,sum(sorted(c[2] for c in leaf)[-2:]))
    print('weighted depths:',[len(code[i]) for i in range(16)])
    for b in (0,1):
        ct=encrypt(code,b,lambda:rng.randrange(2),lambda i,v:v)
        for i,j in combinations(range(16),2):assert decrypt(code,ct,{i:1,j:1},lambda a,v,w:v)==b
    # Check the supplied original assignment, rather than just abstract guard indices.
    for word in [(1<<n)-1,0]+[rng.getrandbits(n) for _ in range(50)]:
        trace=labels['trace'](n,g,word)
        cert={i:(word>>(8*i))&255 for i,x in enumerate(guards) if trace[x]}
        assert (len(cert)>=2)==bool(trace[-1])
        if trace[-1]:
            for b in (0,1):
                def enc(i,v):
                    return v if any(labels['checkkey'](keys[i],w) for w in range(256)) else 0
                ct=encrypt(code,b,lambda:rng.randrange(2),enc)
                actual={i:sum((x>>p&1)<<j for j,p in enumerate(wm[i])) for i,x in cert.items()}
                def dec(i,v,w):
                    assert labels['checkkey'](keys[i],w)
                    return v
                assert decrypt(code,ct,actual,dec)==b
    if planner is not None:planner['compare'](n,g,guards,nand,labels,shapes,front,128,16)
    for d in (3,5,8,16,128):
        c=codes([[i] for i in range(d)],[1]*d)
        print('2-of-n / prefix encryptions / selected decryptions',d,sum(map(len,c.values())),2)

def audit():
    from collections import Counter
    from functools import cache
    rng=Random(784);certified=0;monotones=0
    d=4
    for table in range(1<<(1<<d)):
        if any((table>>x&1) and not (table>>(x|1<<i)&1) for x in range(1<<d) for i in range(d)):continue
        monotones+=1;f=lambda x:(table>>x)&1
        groups=parts(d,f)
        if groups is not None:
            certified+=1
            assert all(bool(f(x))==(sum(any(x>>i&1 for i in g) for g in groups)>=2) for x in range(1<<d))
    groups=[[0,2],[1,3,4],[5]];code=codes(groups,[2,3,4,8,5,1])
    for group in groups:
        jmax=max(map(len,code.values()));bins=[Counter(),Counter()]
        for b in (0,1):
            for r in product(range(2),repeat=jmax):
                v=iter(r);ct=encrypt(code,b,lambda:next(v),lambda i,x:x)
                bins[b][tuple(tuple(ct[i]) for i in group)]+=1
        assert bins[0]==bins[1]
    optimal=0
    for d in range(2,7):
        for _ in range(12):
            w=[rng.randrange(1,51) for j in range(d)]
            @cache
            def opt(mask):
                if mask&(mask-1)==0:return 0
                anchor=mask&-mask;sub=(mask-1)&mask;best=None
                while sub:
                    if anchor&sub:
                        val=opt(sub)+opt(mask^sub)
                        if best is None or val<best:best=val
                    sub=(sub-1)&mask
                return sum(z for i,z in enumerate(w) if mask>>i&1)+best
            c=codes([[i] for i in range(d)],w)
            assert sum(len(c[i])*w[i] for i in c)==opt((1<<d)-1);optimal+=1
    print('monotone tables / recognized / small weighted optima:',monotones,certified,optimal)
if __name__=='__main__':
    import sys,runpy
    audit();controls(*(runpy.run_path(p) for p in sys.argv[1:]))
~~~

~~~python
"""A bounded interval planner for distinct authorized pairs."""
from functools import cache
from itertools import combinations,product
from random import Random

def macro_key(n,g,guards,lo,hi,t,base,labels):
    leaves=guards[lo:hi];used=set(leaves)
    for j in reversed(range(len(g))):
        if n+j+1 in used:used.update(g[j])
    xs=sorted(x for x in used if 1<=x<=n);num=len(xs)
    ren={0:0,**{x:j+1 for j,x in enumerate(xs)}};local=[]
    def N(a,b):local.append((a,b));return num+len(local)
    def neg(a):return N(a,a)
    def both(a,b):return neg(N(a,b))
    def either(a,b):return N(neg(a),neg(b))
    for j,(a,b) in enumerate(g):
        if n+j+1 in used:ren[n+j+1]=N(ren[a],ren[b])
    one=neg(0);two=one
    for x in leaves:
        if t==2:two=either(two,both(one,ren[x]))
        one=either(one,ren[x])
    out=one if t==1 else two;neg(neg(out))
    p=base['schedule'](num,local,[0,len(local)])
    k,ports=labels['canonical'](p,num,0,0,0)
    return k,tuple(xs[p[3][0][i]-1] for i in ports)

def plan(cost,d,objective):
    # Stored columns: residues, preimages, upper MAC count on any honest branch.
    @cache
    def best(a,b,t):
        if b-a<t:return ((0,0,0,0,0),('empty',))
        options=[(cost[a,b,t],('leaf',a,b,t))]
        for k in range(a+1,b):
            if t==1:
                lc,lp=best(a,k,1);rc,rp=best(k,b,1)
                options.append(((lc[0]+rc[0],lc[1]+rc[1],max(lc[2],rc[2]),lc[3]+rc[3],lc[4]+rc[4]),('or',k,lp,rp)))
            else:
                lc,lp=best(a,k,2);rc,rp=best(k,b,2)
                xc,xp=best(a,k,1);yc,yp=best(k,b,1)
                options.append(((lc[0]+rc[0]+xc[0]+yc[0],lc[1]+rc[1]+xc[1]+yc[1],
                                 max(lc[2],rc[2],xc[2]+yc[2]),lc[3]+rc[3]+xc[3]+yc[3],lc[4]+rc[4]+xc[4]+yc[4]),('two',k,lp,rp,xp,yp)))
        return min(options,key=lambda v:(v[0][objective],v[0][0],v[0][1],v[0][2]))
    return best(0,d,2)

def enc(node,b,coin,leaf):
    op=node[0]
    if op=='empty':return None
    if op=='leaf':return leaf(node[1:],b)
    if op=='or':return (enc(node[2],b,coin,leaf),enc(node[3],b,coin,leaf))
    r=coin()
    return (enc(node[2],b,coin,leaf),enc(node[3],b,coin,leaf),
            enc(node[4],r,coin,leaf),enc(node[5],r^b,coin,leaf))

def dec(node,ct,active,leaf):
    op=node[0]
    if op=='empty':return None
    if op=='leaf':return leaf(node[1:],ct)
    k=node[1];left=[x for x in active if x<k];right=[x for x in active if x>=k]
    if op=='or':
        if not active:return None
        return dec(node[2],ct[0],left,leaf) if left else dec(node[3],ct[1],right,leaf)
    if len(left)>=2:return dec(node[2],ct[0],left,leaf)
    if len(right)>=2:return dec(node[3],ct[1],right,leaf)
    if not left or not right:return None
    a=dec(node[4],ct[2],left,leaf);b=dec(node[5],ct[3],right,leaf)
    return None if a is None or b is None else a^b

def compare(n,g,guards,base,labels,shapes,front,alpha,tau):
    d=len(guards);cost={};pred={};hw={}
    for a in range(d):
        for b in range(a+1,d+1):
            for t in (1,2):
                if b-a<t:continue
                key,ports=macro_key(n,g,guards,a,b,t,base,labels)
                h,w=shapes['matrix_shape'](key,front['compile_program']);assert h>=2
                hw[a,b,t]=(h,w);m=alpha*w
                columns=2*((h-2)*m+tau)
                cost[a,b,t]=(2*m*(1+tau)+2*(h-2)*m*m,columns,(h-2)*m*m+m*tau,columns*m,columns*m*(m-1)//2)
                pred[a,b,t]=(key,ports)
    rng=Random(701)
    print('whole with scalar samples and triangular updates',cost[0,d,2])
    for obj in (0,1,3,4):
        counts,node=plan(cost,d,obj);print('interval objective, ciphertext residues / preimage columns / selected MAC ceiling:',obj,*counts)
        emitted=[]
        enc(node,0,lambda:0,lambda k,v:emitted.append(k))
        assert tuple(sum(cost[k][j] for k in emitted) for j in (0,1,3,4))==tuple(counts[j] for j in (0,1,3,4))
        # Bound independent of the common integer scale a>=1 and 1<=t<=a*min_width.
        hwlist=[hw[k] for k in emitted];H,W=hw[0,d,2];z=min([W]+[w for h,w in hwlist])
        middle=sum((h-2)*w*w for h,w in hwlist);sw=sum(w for h,w in hwlist)
        capC=middle+(z+1)*sw;capS=middle+z*sw
        capT=sum(((h-2)*w+z)*w*w for h,w in hwlist)
        baseC=(H-2)*W*W;baseT=baseC*(W-1)
        maxD=0;observed=0
        # Evaluate all abstract availability patterns with exactly two guards.
        for pair in combinations(range(d),2):
            for msg in (0,1):
                def check(k):
                    a,b,t=k;return sum(a<=i<b for i in pair)>=t
                ct=enc(node,msg,lambda:rng.randrange(2),lambda k,s:s if check(k) else 0)
                used=[]
                def recover(k,v):
                    assert check(k);used.append(k);return v
                assert dec(node,ct,pair,recover)==msg
                observed=max(observed,sum(cost[k][2] for k in used))
                maxD=max(maxD,sum((hw[k][0]-2)*hw[k][1]**2+z*hw[k][1] for k in used))
        assert observed==counts[2]
        if obj==0:
            print('fixed layout, min width, scale-free upper/baseline pairs (C,S,T,D):',
                  z,(capC,baseC),(capS,baseC),(capT,baseT),(maxD,baseC))
            assert 100*capC < 65*baseC and 100*capS < 65*baseC
            assert 100*capT < 40*baseT and 100*maxD < 22*baseC
        # For real original witnesses verify every selected aggregate predicate.
        for word in [0,(1<<n)-1]+[rng.getrandbits(n) for _ in range(20)]:
            tr=labels['trace'](n,g,word);live=[i for i,x in enumerate(guards) if tr[x]]
            if len(live)<2:continue
            for bit in (0,1):
                # Positive-path audit oracle; NO privacy is argued by composition.
                ct=enc(node,bit,lambda:rng.randrange(2),lambda k,b:b)
                def check_witness(k,v):
                    key,ports=pred[k];w=sum((word>>(x-1)&1)<<j for j,x in enumerate(ports))
                    assert labels['checkkey'](key,w)
                    return v
                assert dec(node,ct,live,check_witness)==bit
~~~

### Serialized lattice composition and the number of root rows

The fourth listing plugs a small actual lattice-chain Enc/Dec into the prefix compiler. Its three guards are distinct two-literal clauses on disjoint pairs of private bits. A two-of-three policy has five encrypted local bits. Every leaf uses two encoded layers, two terminal columns, modulus 7^28 and an integer-centered threshold floor(q/4096) fixed before encryption. Residues are serialized in ten bytes each. Dec receives only the selected serialized leaf records, their public layout and the local witnesses. The diagnostic separately checks all preimage congruences and the noise residual on every path. The trapdoor construction, floating QR and Gaussian decisions are adapted from the [PR 99 correctness diagnostic](https://github.com/MachinaIO/SigabaPark/pull/99); this uses reduced dimensions, seeded test streams and unbounded toy proposal loops. It does not instantiate concrete quantum security or a worst-case sampler clock.

| Lattice dimension | Retained root rows | Bytes per outer bit | Valid opens passed / failed |
| ---: | ---: | ---: | ---: |
| 4 | 1 | 49200 | 96 / 12 |
| 4 | 2 | 65600 | 108 / 0 |
| 8 | 1 | 97200 | 108 / 0 |

Each row comprises both outer messages and all qualifying six-bit witnesses. It performs 216 leaf decryptions and checks 40 exact residuals across ten leaf encryptions. The failures at dimension four all stem from one valid local path with bit-one payload and identically zero ideal integer signal. The two-row replay preserves the first row, the chosen tensor matrices, the trapdoors and the final columns using the same primary stream, generating only the extra root noise from a separate stream. The second row fixes this failure on the tested instance. Relative to doubling the dimension, the two-row replay uses 31600 fewer bytes here. This comparison concerns correctness on these coins, not equivalent hardness.

Retaining l root rows is again public postprocessing of the full ciphertext. For the two-layer backend there is also a simple correctness estimate. Let p be the underlying prime and let rho bound the maximum single-entry atom modulo p of the independent tensor matrices. For the bit-one guard path the logical row contains a unit. Given a terminal tensor factor S2 of rank r modulo p, each independent selected root row of S1 annihilates S2 with probability at most rho^r, by conditioning on all but r pivot coordinates. All l rows annihilate it with probability at most rho^(r l). For any 1<=k<=n, the probability rank(S2)<k is at most binom(n,k-1) rho^((n-k+1)^2): choose k-1 columns spanning the others (extend a spanning selection if needed), then each remaining independent column must satisfy at least n-k+1 independent constraints. Thus the total signal-loss probability is at most that term plus rho^(k l), capped at one. A surviving row and t nearly uniform final columns give the terminal small-interval bound of PR 99; add its statistical and evaluation-error terms. For longer chains the conditional rank argument still applies to the suffix product, whose rank distribution is bounded in the final section below. The extra rows increase the actual transmitted root size and selected arithmetic. Run OPENBLAS_NUM_THREADS=1 python lattice.py frontend.py pair.py with NumPy to reproduce the toy checks.

~~~python
from itertools import product
from math import ceil,exp,pi
from random import Random
import numpy as np

def exercise(front,wrapper,n,roots):
    rng=Random(60414);extra=Random(50718);share_rng=Random(7103)
    q=7**28;rad=256;k=ceil(q.bit_length()/8);t=2
    public_B=q//4096;bytes_per=(q.bit_length()+7)//8
    clauses=[(1,2),(1,-2),(-1,2)]
    def arr(r,c,f):return np.array([[f() for _ in range(c)] for _ in range(r)],dtype=object)
    def digits(z):
        z=z.copy()%q;rows=[]
        for _ in range(k):rows.append(z%rad);z=z//rad
        assert not z.any()
        return np.stack(rows,axis=1).reshape((-1,z.shape[1]))
    def gauss(center,width,stream=None):
        stream=rng if stream is None else stream
        lo=int(np.floor(center-12*width));hi=int(np.ceil(center+12*width))
        while True:
            j=stream.randint(lo,hi)
            if stream.random()<exp(-pi*((j-center)/width)**2):return j
    u0,_=front['compile_program']([clauses[0]],2,0)
    w=len(u0);d=n*w;a=4;m=a+d*k;I=np.eye(a,dtype=object)
    G=np.kron(np.eye(d,dtype=object),np.array([[rad**j for j in range(k)]],dtype=object))
    def trap():
        A0=arr(d,a,lambda:rng.randrange(q));S=arr(a,d*k,lambda:rng.randrange(-1,2))
        A=np.hstack((A0,(G-A0@S)%q))
        one=np.zeros((k,k),dtype=object)
        for j in range(k-1):one[j,j]=rad;one[j+1,j]=-1
        rem=q
        for j in range(k):rem,digit=divmod(rem,rad);one[j,-1]=digit
        assert rem==0
        block=np.kron(np.eye(d,dtype=object),one)
        lift=digits(-A0)
        basis=np.block([[S@block,I+S@lift],[block,lift]])
        assert not ((A@basis)%q).any()
        # Each gadget kernel has determinant q. The remaining columns project to
        # the identity on top coordinates after undoing the unit shear.
        ortho,tri=np.linalg.qr(np.asarray(basis,float))
        sigma=16*abs(np.diag(tri)).max()
        def preimages(target):
            y0=digits(target);y=np.vstack((S@y0,y0))
            centers=ortho.T@np.asarray(y,float)
            for j in reversed(range(m)):
                width=sigma/abs(tri[j,j])
                z=[gauss(-c/tri[j,j],width) for c in centers[j]]
                centers[:j]+=np.outer(tri[:j,j],z)
                y+=np.outer(basis[:,j],np.array(z,dtype=object))
            assert not ((A@y-target)%q).any()
            return y
        return A,preimages

    code=wrapper['codes']([[0],[1],[2]],[1,1,1])
    badleaf=[];samples=0;residuals=0;dec_calls=0;passed=0;failed=0
    def enc_leaf(i,msg):
        nonlocal samples,residuals
        u,layers=front['compile_program']([clauses[i]],2,msg)
        assert len(u)==w and len(layers)==2
        A0,pre=trap();Af=arr(d,t,lambda:rng.randrange(q))
        buf=[];plain=[];enc=[]
        for j,branches in enumerate(layers):
            Fpair=[];Cpair=[]
            for edges in branches:
                M=np.zeros((w,w),dtype=object)
                for src,dst in edges:M[src,dst]=1
                S=arr(n,n,lambda:gauss(0,2.5))
                F=np.kron(np.array([u],dtype=object)@M,S)[:roots] if j==0 else np.kron(M,S)
                A=A0 if j==0 else Af
                if j==0:
                    noise=arr(1,A.shape[1],lambda:gauss(0,2))
                    if roots>1:noise=np.vstack((noise,arr(roots-1,A.shape[1],lambda:gauss(0,2,extra))))
                else:noise=arr(F.shape[0],A.shape[1],lambda:gauss(0,2))
                target=(F@A+noise)%q
                C=target if j==0 else pre(target)
                if j:samples+=t
                Fpair.append(F);Cpair.append(C)
                buf.append(b''.join((int(x)%q).to_bytes(bytes_per,'little') for x in C.flat))
            plain.append(Fpair);enc.append(Cpair)
        for a,b in product((0,1),repeat=2):
            err=(enc[0][a]@enc[1][b]-plain[0][a]@plain[1][b]@Af+q//2)%q-q//2
            assert max(map(abs,err.flat))<=public_B;residuals+=1
            if any((a,b)[abs(v)-1]==(v>0) for v in clauses[i]):
                obs=(enc[0][a]@enc[1][b]+q//2)%q-q//2
                if int(max(map(abs,obs.flat))>public_B)!=msg:
                    badleaf.append((i,msg,a,b,not (plain[0][a]@plain[1][b]).any()))
        return b''.join(buf)
    def dec_leaf(i,blob,word):
        nonlocal dec_calls
        dec_calls+=1
        a,b=word&1,word>>1&1
        def fetch(start,count):
            return np.array([int.from_bytes(blob[j:j+bytes_per],'little') for j in
                range(start*bytes_per,(start+count)*bytes_per,bytes_per)],dtype=object)
        root=fetch(a*roots*m,roots*m).reshape(roots,m);last=fetch(2*roots*m+b*m*t,m*t).reshape((m,t))
        observed=(root@last+q//2)%q-q//2
        return int(max(map(abs,observed.flat))>public_B)
    for bit in (0,1):
        ct=wrapper['encrypt'](code,bit,lambda:share_rng.randrange(2),enc_leaf)
        size=sum(len(x) for row in ct.values() for x in row)
        for word in range(64):
            cert={}
            for i,clause in enumerate(clauses):
                v=word>>(2*i)&3
                if any(((v>>(abs(x)-1))&1)==(x>0) for x in clause):cert[i]=v
            if len(cert)<2:continue
            before=dec_calls;out=wrapper['decrypt'](code,ct,cert,dec_leaf);assert dec_calls-before==2
            if out==bit:passed+=1
            else:failed+=1
        print('end-to-end bit / serialized payload bytes / matrix columns',bit,size,m)
    print('valid opens passed / failed, leaf decryptions, exact residuals, sampled columns:',
          passed,failed,dec_calls,residuals,samples)
    print('dimension / root rows and erroneous valid leaf paths (id,msg,a,b,zero integer signal):',n,roots,badleaf)
    return failed
if __name__=='__main__':
    import sys,runpy
    front,wrapper=[runpy.run_path(p) for p in sys.argv[1:]]
    exercise(front,wrapper,4,1)
    assert exercise(front,wrapper,4,2)==0
    assert exercise(front,wrapper,8,1)==0
~~~


### Correctness through arbitrary chain depth

The following calculation applies directly to the polynomial NAND compiler in PR 99. Fix a valid witness before sampling Enc. For modulus q=p^k assume every selected n-by-n tensor factor has independent entries modulo p with maximum atom at most rho<1, and successive factors are independent. Start from l distinct standard rows, 1<=l<=n. Track the rank over F_p after each multiplication. Rank zero is absorbing.

For each prefix rank r let K[r,s] be the rank distribution after n steps of this auxiliary process: start at d=0; stay at d with probability rho^(r-d), otherwise increase by one. Indeed, given a prefix matrix of rank r and previously exposed output columns spanning dimension d, the next output column stays in that span only if the independent fresh input column solves r-d independent linear equations. After conditioning on its nonpivot entries the pivot entries are fixed, giving the claimed upper bound on the stay probability. Thus the actual new rank stochastically dominates this auxiliary law. Couple successive column tests by common uniform draws: at equal dimensions the real process jumps with at least the auxiliary probability, while a one-column jump cannot cross a strict lead. The same coupling shows the auxiliary final dimension is stochastically increasing in the starting prefix rank r. Induction over H independent factors now bounds simultaneous loss of all selected rows by (K^H)[l,0]. For independent uniform entries and rho=1/p the constraint probability is exact and so is the rank law. For one row this recovers 1-(1-rho^n)^H.

For a valid bit-one path the logical message coordinate is a unit. On rank survival, choose the first surviving row as a function of the tensor factors. It has a unit coefficient over Z/q, so independent uniform terminal columns yield independent uniform evaluations on that row. In the notation of PR 99 the per-witness bit-one failure bound is epsilon_eval + eta + (K^H)[l,0] + ((4B+1)/q)^t. This charges the evaluation-error event for all retained entries and the statistical distance of the final public matrix. It requires no independence between the observed errors and the ideal signal. Bit zero only incurs the evaluation-error term. A simultaneous guarantee across witnesses would require additional accounting. See [VWW Construction 4.2 and Lemma 4.3](https://eprint.iacr.org/2022/1140.pdf).

For H>=2 the ciphertext uses 2lm+2(H-2)m²+2mt residues. Selected dense Dec uses l((H-2)m²+mt) multiply-accumulates plus access, witness processing and classification. If H=1, transmit 2lt residues. Extra root rows can be generated with the existing public matrices and require additional root arithmetic and fresh error entries, but no extra trapdoor or preimage column. These are polynomial changes to the honest algorithms. The transmitted view is deterministic postprocessing of the full ciphertext. The backend's security assumptions still apply.

At H=4096 and rho=1/2 the entries below give b such that the rank-loss term is at most 2^-b. Dimension n is the tensor dimension. The chosen rho is illustrative and must be checked for the instantiated entry law.

| n | One row | Two rows | Three rows |
|---:|---:|---:|---:|
|32|20|39|58|
|64|52|103|154|
|128|116|231|346|

The auxiliary kernel costs O(n l²) arithmetic steps with precomputed atom powers, and powering costs O(l³ log H) arithmetic steps. The fifth listing, survival.py, builds the kernel exactly and rounds every powered matrix entry upward to a dyadic with 512 fractional bits for the table. All entries are nonnegative, preserving the upper bound. Running python survival.py also checks small uniform and biased cases by exhaustive enumeration.

~~~python
"""Certified upper bound on loss of all retained rows along one fixed witness path."""
from fractions import Fraction
from itertools import product
from math import comb

def kernel(n,l,rho):
    assert 1<=l<=n and 0<rho<1
    out=[]
    for r in range(l+1):
        prob=[Fraction(1)]+[Fraction(0)]*l
        for j in range(n):
            nxt=[Fraction(0)]*(l+1)
            for s in range(r+1):
                stay=rho**(r-s)
                nxt[s]+=prob[s]*stay
                if s<r:nxt[s+1]+=prob[s]*(1-stay)
            prob=nxt
        assert sum(prob)==1
        out.append(prob)
    return out
def upper(n,l,H,rho,precision):
    assert H>=1 and precision>=1
    den=1<<precision
    K=kernel(n,l,rho)
    mat=[[(v.numerator*den+v.denominator-1)//v.denominator for v in row] for row in K]
    acc=[[den*int(i==j) for j in range(l+1)] for i in range(l+1)]
    def mul(A,B):
        return [[(sum(A[i][k]*B[k][j] for k in range(l+1))+den-1)//den
                 for j in range(l+1)] for i in range(l+1)]
    while H:
        if H&1:acc=mul(acc,mat)
        H//=2
        if H:mat=mul(mat,mat)
    return Fraction(min(den,acc[l][0]),den)
def audit():
    # Enumerate uniform binary n=2 tensor factors, then compare the exact rank law.
    n=2
    for l in (1,2):
        states={tuple(1<<i for i in range(l)):1}
        K=kernel(n,l,Fraction(1,2))
        weights=[Fraction(int(i==l)) for i in range(l+1)]
        for H in range(1,5):
            out={}
            for rows,count in states.items():
                for cols in product(range(1<<n),repeat=n):
                    rr=tuple(sum(((x&c).bit_count()%2)<<j for j,c in enumerate(cols)) for x in rows)
                    out[rr]=out.get(rr,0)+count
            states=out
            weights=[sum(weights[i]*K[i][j] for i in range(l+1)) for j in range(l+1)]
            actual=Fraction(states.get((0,)*l,0),sum(states.values()))
            assert actual==weights[0] and actual<=upper(n,l,H,Fraction(1,2),40)
    # Also enumerate biased binary factors and compare to the max-atom upper bound.
    for l in (1,2):
        states={tuple(1<<i for i in range(l)):1}
        for H in range(1,4):
            out={}
            for rows,count in states.items():
                for cols in product(range(4),repeat=2):
                    rr=tuple(sum(((x&c).bit_count()%2)<<j for j,c in enumerate(cols)) for x in rows)
                    mass=3**(4-sum(c.bit_count() for c in cols))
                    out[rr]=out.get(rr,0)+count*mass
            states=out
            assert Fraction(states[(0,)*l],sum(states.values()))<=upper(2,l,H,Fraction(3,4),64)
    for n in (32,64,128):
        for l in (1,2,3):
            v=upper(n,l,4096,Fraction(1,2),512)
            # Largest integer b with v<=2^-b.
            b=(v.denominator//v.numerator).bit_length()-1
            assert v*(1<<b)<=1 and v*(1<<(b+1))>1
            print('dimension / root rows / certified bits against row loss alone',n,l,b)
if __name__=='__main__':audit()
~~~
