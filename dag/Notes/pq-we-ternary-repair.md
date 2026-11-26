---
title: Bounded ternary repair certificates and finite-clock one-bit WE for recognized 3-CNF
refs: [definition:WE_CircuitSAT, note:pq-we-split-witness-abe, theorem:AdvancedEncryption.WE.CNF.bounded_repair_complete]
tags: [witness-encryption, circuit-sat, attribute-based-encryption]
---

For 128-variable NAND statements that can be converted exactly to 3-CNF on the original variables, we give two different uses of clause-guided repair. One spends public search time at encryption and sends one classical bit. The other converts a *given* satisfying assignment to a shorter certificate with a fast nearest-center algorithm and uses split-witness ABE. They have different costs and correctness budgets. Neither assumes all registered NAND circuits have a small 3-CNF. This uses the walk from [Schöning, FOCS 1999](https://www.eecs.harvard.edu/~michaelm/CS223/schoning99.pdf) and the covering-code / Hamming-ball viewpoint in [Moser and Scheder](https://arxiv.org/abs/1008.4067). No improvement of the best 3-SAT decision exponent is claimed.

**Public format check.** Propagate a CNF for each wire and its complement. For NAND, the negative polarity conjoins the positive children, and the positive polarity distributes disjunction over the negative children. Swap polarities for a self-NAND. Normalize forward reads to constant true at the point of use. Discard tautological clauses, cap width at three and limit both clause counts and attempted distribution products. An abandoned polarity may still occur in a simplification by a known constant; otherwise its derived result is abandoned. Induction on wire order proves that every returned formula computes exactly the original Boolean function. On failure, use the original construction. In particular a Tseitin conversion adding a variable for each gate cannot be used with the numerical 128-variable bounds below.

**The repair verifier.** If the current assignment satisfies F, it remains fixed. Otherwise take the first violated clause in a public order and use the next ternary digit to select a literal, reducing the digit modulo the clause length for a short clause. Flip its variable. Reject an empty clause. For any fixed satisfying target w, at least one of the selected clause's variables disagrees with w. Choosing that position removes precisely one disagreement. From any anchor within radius r, the holder of w can generate exactly r digits leading to an accepting assignment (pad after early success). Conversely every successful path ends at an assignment satisfying F. The Lean theorem bounded_repair_complete proves the fixed-length path implication over Boolean assignments from these two literal conditions. It does not formalize the probability calculations or the NAND-to-CNF compiler.

**Assumption-free encryption by a bounded random walk.** Start uniformly on the cube and use T independent uniform ternary choices. For a fixed target at distance d, success by T steps is lower-bounded by the probability of hitting zero on the nonnegative integer line with downward probability 1/3 and upward probability 2/3. One coupling chooses a uniform random number each step and makes each true decrease contain the event of a comparison-walk decrease. From equal distances this respects ordering, and unequal distances of the two walks have even difference before stopping, so one step cannot cross. Additional satisfying states only help. If all choices decrease at distance n the same bound remains valid. With absorption at zero, define integer counts H_0(0)=1, H_0(d>0)=0, H_t(0)=3^t and H_t(d)=H_(t-1)(d-1)+2H_(t-1)(d+1). Average H_T(d)/3^T against Binomial(128,1/2).

To realize the ternary choices with a fixed tape clock, draw s=ceil(log2(3^T))+16 fair bits as an integer. If it lies outside the largest initial multiple of 3^T, charge a failed trial. Otherwise take its residue and expand in base three. The resulting unconditional success bound p has denominator 2^(128+s) and numerator floor(2^s/3^T) times the binomially weighted sum of H_T. Independent trials J=ceil(89/p) have failure at most exp(-89)<2^-128. Encrypt the bit AND the success flag; decryption returns the ciphertext bit. On a false formula the ciphertext is zero for either message, independently of all coins. Enumeration of T=0,...,384 with exact integer arithmetic minimizes the displayed bound on total CNF checks at **T=165, s=278, J=1,021,393,308,818,026,961**, at most **169,551,289,263,792,475,526** CNF checks (about 2^67.20). These are derived caps, not measured run times. Each check can scan the entire CNF; random-bit generation, parsing, copying and machine description also cost resources. Positive instances may stop early. This yields a finite, specified completeness bound, without issuing any ABE keys.

**Public shifted codes for witness conversion.** Fix a small code C in 16 bits. Take its Cartesian product over eight disjoint blocks. Encryption publishes J independent uniform 128-bit shifts of this product. For each shift the witness holder independently picks the closest member of C in each shifted 16-bit block. If the total distance is at most r, use the shift number, the eight indices and the repair digits. The total number of possible certificates is N=J·|C|^8·3^r. For any fixed satisfying witness, the distance to one shifted product has exactly the distribution of the sum of eight independent distances of uniform 16-bit words to C. We enumerate the single-block histogram and convolve it eight times; if p is the resulting mass at distance ≤r, the miss probability is exactly (1-p)^J. The integer script upper-rounds every multiplication at 192 fractional bits before checking against 2^-129. This correctness bound is per witness as required by Def_WE. If ABE decryption on an authorized pair fails with probability at most 2^-129, the total per-witness error is at most 2^-128 by the union bound.

The span in the third row below is the set of truth tables of affine functions of four input bits (32 codewords). The other two rows use the length-16 repetition code {all-zero,all-one}. A center lookup costs at most J·8·|C| sixteen-bit distance checks; it does not enumerate all J·|C|^8 centers.

| J | C size | r | log2 N | Worst-case 16-bit distance checks by witness holder | Public shift bits |
|---:|---:|---:|---:|---:|---:|
| 190490 | 2 | 38 | 85.77 | 3047840 | 24382720 |
| 9842 | 2 | 42 | 87.83 | 157472 | 1259776 |
| 92 | 32 | 31 | 95.66 | 23552 | 11776 |

**Terminal ABE.** For c trailing digits the key table has J·|C|^8·3^(r-c) entries and the ciphertext table 3^c. Under one fresh KP-ABE setup, each key fixes one actual anchor and the first r-c repairs. The encryptor can run these fixed repairs in the clear and hardwire the resulting 128-bit assignment into the predicate. The remaining predicate simulates c ternary choices and tests satisfaction; invalid encodings reject. This avoids selecting a shift or decoding a product code inside the policy. For the first row c=27 gives **8,638,651,399,680 keys and 7,625,597,484,987 ciphertexts** versus 2^64 of each in the raw 128-bit split. Even after center lookup and prefix precomputation, the predicates can have substantial sequential depth from up to 27 first-violated-clause searches. The message-switch proof conditions on the public shifts. On a false formula no path can accept under any issued key, so each hybrid challenges an unauthorized attribute under the same setup. Use the split-witness reduction of PR #64. The table sizes exclude ABE parameter, key-generation, policy-compilation and sequential lookup costs. In particular these figures cannot be substituted for the complete Ring-LWE cost estimate in PR #83.

**Measured policy cost on the planted control.** Compile the actual selected functional-key predicate for the 190,490-shift setting. Shift index 703 yielded a near anchor. The first 11 repair choices were fixed in the key and evaluated before compilation. For each remaining digit use a balanced OR tree plus a prefix scan to find the first violated clause; group its three possible flips by variable, apply one flip, and check satisfaction after 27 rounds. Two public attribute bits encode each trit; the circuit rejects 11. A structurally hashed AND/inverter DAG was converted to fan-in-two NANDs with required inverters, output reachability and constant folding. This yielded **89,422 NANDs at depth 1,039** for this key, compared with **450 NANDs at depth 22** for the same CNF and the same compiler with the planted first 64 original bits fixed in an ordinary balanced split. The source NANDs contain padding. Both comparisons use the recovered CNF. The depth figures are binary NAND depths, not BGG+ effective noise bounds. The accepting path, 20 additional seeded ternary inputs, and an invalid two-bit encoding were checked. This is one measured pair of key predicates, with a roughly 47-fold depth increase. A uniform parameter choice must handle all keys, not just this pair. The table-entry reduction alone cannot establish an end-to-end improvement.

The same compiler admits a conservative bound uniform over keys for a fixed CNF. For m≥1 nonempty clauses (each of width at most three), put h=ceil(log2 m), L=2^h. One round adds at most 6m+2L+8n+5 binary AND nodes with free complements: 2m for the violated-clause flags, L-1 for the tree and L-1 for prefix enables, m leaf selects, at most 3m for the per-position group reductions, 8n for masks and XOR updates, and at most five for digit decoding/validity. The AIG depth increment is at most 3h+8: two levels for a clause, at most 2h+1 to select the first violation, h for the group OR, then five for masking, OR and XOR. The validity chain also fits this bound. The final satisfaction test adds at most 3m+1 AND nodes and h+3 levels. An AIG of G gates and depth D on 2c inputs lowers here to at most 2G+2c+1 NANDs and depth at most 2D+1 (one physical NAND per AND and at most one inverter per needed polarity). At n=128, m=300 and c=27, these bounds give 209,919 NANDs and depth 1,915 or less for every fixed key of the example; they still exclude lattice costs. Empty clauses can be handled immediately as false.

A second implementation uses a divide-and-conquer parallel-prefix OR for all preceding violation flags. At each doubling, every position in the right half of a block combines its prefix with the final prefix of the left half. This computes all prefixes in h AIG levels with more gates. On the same key it used **110,204 NANDs at depth 835**, reducing depth by 204 and adding 20,782 NANDs. The preceding uniform gate bound is for the first implementation. For the parallel-prefix version a conservative AIG depth increment is 2h+8 per round (clause flags, prefix OR and one select, variable-group OR and final update), giving a uniform NAND depth bound of 1,429 for these parameters. The two circuits implement the same 27-trit policy.

**An alternate center-access tradeoff.** For 31 repairs take 120 independent affine maps from 29 bits to 128 bits, sampled as binary matrices plus offsets. Each map gives 2^29 pairwise independent uniform anchors, with repetitions allowed. For a fixed target let p=Vol(128,31)/2^128. For X the number of hits, E[X]=2^29 p, Var(X)=2^29 p(1-p); the second-moment bound gives Pr[X=0]≤(1-p)/(1-p+2^29 p). Raising this bound to power 120 gives at most 2^-129 by integer comparison. The maps need 460,800 public bits. There are 120·2^29·3^31 certificate labels, about 2^85.04; testing all 64,424,509,440 anchors in the worst case is much more costly for the witness holder. This illustrates why center lookup and seed size must accompany the certificate length.

**Evidence.** Standalone scripts follow. The full-size SAT control is a planted 300-clause CNF compiled to exactly 4,096 NAND gates. The UNSAT variant replaces eight clauses by clauses excluding all assignments on three variables. The compiler recognizes both without auxiliary variables. A fixed test stream with the 9,842-shift code found a close center on shift index 48, generated an accepting certificate and rejected that certificate on the UNSAT control. Tests include all 625 two-input two-gate lists, 400 seeded small circuits, every starting point for each satisfying target of a small repair formula, and arbitrary three-digit paths on a contradiction. The reference encryptor has a finite fallback on unrecognized NANDs. The full-size random-walk trial budget and full ABE tables were not executed; neither a registered machine clock nor a quantum-secure ABE parameter instantiation has been verified here.

### Exact walk and affine-map bounds

~~~python
from math import comb,log2
n=128
ceildiv=lambda a,b:(a+b-1)//b
H=[1]+[0]*386
best=None
for t in range(385):
    if t:
        H=[3**t]+[H[d-1]+2*H[d+1] for d in range(1,len(H)-1)]+[0]
    d3=3**t
    s=(d3-1).bit_length()+16
    good=sum(comb(n,d)*H[d] for d in range(n+1))*((1<<s)//d3)
    den=1<<(n+s)
    trials=ceildiv(89*den,good)
    cand=((t+1)*trials,t,trials,s)
    if best is None or cand<best:best=cand
print('walk',best,log2(best[0]))
# Public affine pairwise-independent anchors index d over F2^a, independent books; reserve half the correctness budget.
# Second moment bound for zero hits <= (1-p)/(1-p+L*p).
# Different books independent. Use c books, smallest power-of-two L allowing this failure bound.
def needed_books(a,volume):
    d=1<<128
    A=d-volume
    B=A+(1<<a)*volume
    if (A<<129)<=B:return 1
    lo,hi=1,129
    if (A**hi<<129)>B**hi:return None
    while hi-lo>1:
        m=(hi+lo)//2
        if (A**m<<129)<=B**m:hi=m
        else:lo=m
    return hi
scores=[]
for r in range(1,65):
    v=sum(comb(n,j) for j in range(r+1))
    for a in range(max(0,n-v.bit_length()-1),min(60,n-v.bit_length()+14)+1):
        c=needed_books(a,v)
        if c is None:continue
        N=c*(1<<a)*3**r
        scores.append((N,r,a,c, (c*(1<<a)-1).bit_length()))
best=min(scores)
print('book',best,log2(best[0]),'split',log2(best[0])/2)
for cap in [25,28,30,32,34,36,38,40]:
    w=min((q for q in scores if q[4]<=cap),default=None)
    if w:print(cap,w[1:],log2(w[0]))
~~~

### Shifted product-code bounds

~~~python
from math import comb,log2,isqrt
from collections import Counter
from fractions import Fraction

def words(b,d):
    basis=[(1<<b)-1]+[sum(((i>>j)&1)<<i for i in range(b)) for j in range(d-1)]
    span=[0]
    for a in basis:span += [w^a for w in span]
    return span

def distance_hist(b,code):
    return Counter(min((x^w).bit_count() for w in code) for x in range(1<<b))

def total_hist(b,code):
    hist=distance_hist(b,code)
    p={0:1}
    for _ in range(128//b):
        q=Counter()
        for i,c in p.items():
            for j,v in hist.items():q[i+j]+=c*v
        p=q
    assert sum(p.values())==1<<128
    return p

def bits_ok(bad,J):
    # Conservative exact certificate from 192 fractional bits, rounded upward.
    scale=1<<192
    x=bad<<64
    y=scale
    while J:
        if J&1:y=(y*x+scale-1)//scale
        x=(x*x+scale-1)//scale
        J>>=1
    return y<=1<<(192-129)

def first(bad,cap):
    if not bits_ok(bad,cap):return None
    lo,hi=0,cap
    while hi-lo>1:
        m=(lo+hi)//2
        if bits_ok(bad,m):hi=m
        else:lo=m
    return hi

results=[]
for b in (8,16):
    for d in range(1,(b.bit_length()-1)+2):
        code=words(b,d)
        hist=total_hist(b,code)
        cumulative=0
        for r in range(max(hist)+1):
            cumulative+=hist.get(r,0)
            J=first((1<<128)-cumulative,1<<18)
            if J:
                anchorbits=d*(128//b)
                N=J*(1<<anchorbits)*3**r
                results.append((N,b,d,r,J,anchorbits, cumulative))
for cap in (1,8,128,1024,1<<14,1<<18):
    w=min(row for row in results if row[4]<=cap)
    print(cap,w[:6],log2(w[0]),'hit',float(Fraction(w[6],1<<128)))
~~~

### Format recognition, repair encoder and direct bit encryptor

~~~python
from itertools import product
from random import Random

def extract(n,g,k=3,cap=8192):
    # None means this polarity was abandoned. () is true and ((),) is false.
    top,bot=(),((),)
    def conj(f,h):
        if bot in (f,h):return bot
        if f is None or h is None:return None
        u=set(f)|set(h)
        return tuple(sorted(u)) if len(u)<=cap else None
    def disj(f,h):
        if top in (f,h):return top
        if f is None or h is None:return None
        if len(f)*len(h)>cap:return None
        result=set()
        for a in f:
            for b in h:
                t=set(a)|set(b)
                if any(-i in t for i in t):continue
                if len(t)>k:return None
                result.add(tuple(sorted(t)))
        return tuple(sorted(result))
    wires=[(top,bot)]+[(((i,),),((-i,),)) for i in range(1,n+1)]
    for a,b in g:
        a=a if a<len(wires) else 0
        b=b if b<len(wires) else 0
        x,nx=wires[a];y,ny=wires[b]
        wires.append((nx,x) if a==b else (disj(nx,ny),conj(x,y)))
    return wires[-1][0] if g else top

def first_bad(F,x):
    return next((row for row in F
                 if not any((x>>(abs(v)-1)&1)==(v>0) for v in row)),None)
def walk(F,x,digits):
    for digit in digits:
        c=first_bad(F,x)
        if c is None:return True
        if not c:return False
        x ^= 1<<(abs(c[digit%len(c)])-1)
    return first_bad(F,x) is None

def repair(F,start,w,r):
    x=start;ds=[]
    for _ in range(r):
        c=first_bad(F,x)
        if c is None:break
        i=next(j for j,v in enumerate(c) if ((w^x)>>(abs(v)-1))&1)
        x ^= 1<<(abs(c[i])-1);ds.append(i)
    return ds+[0]*(r-len(ds))

def nearest(x,delta,b,span,n):
    y=x^delta; anchor=delta; indices=[]
    for j in range(0,n,b):
        block=(y>>j)&((1<<b)-1)
        i=min(range(len(span)),key=lambda i:(span[i]^block).bit_count())
        indices.append(i)
        anchor ^= span[i]<<j
    return anchor,indices

def encode(F,w,shifts,r,b,span,n):
    for j,delta in enumerate(shifts):
        x,idx=nearest(w,delta,b,span,n)
        if (x^w).bit_count()<=r:return j,idx,repair(F,x,w,r)
    return None

def check_code(F,shifts,code,b,span,n,r):
    if code is None:return False
    j,idx,ds=code
    if not (0<=j<len(shifts) and len(idx)==n//b and len(ds)==r
            and all(0<=i<len(span) for i in idx) and all(0<=d<3 for d in ds)):return False
    start=shifts[j]^sum(span[i]<<(k*b) for k,i in enumerate(idx))
    return walk(F,start,ds)

def eval_g(n,g,x):
    w=[1]+[x>>i&1 for i in range(n)]
    for a,b in g:w.append(1-((w[a] if a<len(w) else 1)&(w[b] if b<len(w) else 1)))
    return w[-1] if g else 1

def raw_cnf(n,cs,size):
    g=[]
    def nand(a,b):
        g.append((a,b));return n+len(g)
    def either(a,b):return nand(nand(a,a),nand(b,b))
    def both(a,b):
        t=nand(a,b);return nand(t,t)
    outs=[]
    for row in cs:
        vals=[v if v>0 else nand(-v,-v) for v in row]
        t=vals[0]
        for v in vals[1:]:t=either(t,v)
        outs.append(t)
    while len(g)<size-2*(len(outs)-1):nand(0,0)
    t=outs[0]
    for v in outs[1:]:t=both(t,v)
    assert len(g)==size
    return g

def small(n,g):
    F=extract(n,g)
    if F is not None:
        for x in range(1<<n):assert (first_bad(F,x) is None)==bool(eval_g(n,g,x))
for a,b,c,d in product(range(5),repeat=4):small(2,[(a,b),(c,d)])
rr=Random(851)
for _ in range(400):
    n=rr.randrange(8);s=rr.randrange(12)
    small(n,[(rr.randrange(n+s+1),rr.randrange(n+s+1)) for _ in range(s)])
n=128;w=rr.getrandbits(n)
cs=[]
for _ in range(300):
    vs=rr.sample(range(1,129),3)
    row=[v if rr.randrange(2) else -v for v in vs]
    if first_bad([row],w) is not None:row[0]*=-1
    cs.append(row)
for no in (False,True):
    rows=cs.copy()
    if no:rows[:8]=[[(1+i)*(1 if t else -1) for i,t in enumerate(bits)] for bits in product(range(2),repeat=3)]
    g=raw_cnf(n,rows,4096);F=extract(n,g)
    assert F is not None and len(F)==len(set(tuple(sorted(row)) for row in rows))
    for _ in range(200):
        x=rr.getrandbits(n)
        assert (first_bad(F,x) is None)==bool(eval_g(n,g,x))
    shifts=[rr.getrandbits(n) for _ in range(9842)]
    span=[0,65535]
    if not no:
        code=encode(F,w,shifts,42,16,span,n)
        assert check_code(F,shifts,code,16,span,n,42)
        print('full-size SAT',len(F),'clauses; first successful shift (zero-based)',code[0])
    else:
        assert not check_code(F,shifts,code,16,span,n,42)
        print('full-size UNSAT',len(F),'clauses; previous certificate rejected')

# Exhaust the repair rule and arbitrary decoder words on four variables.
F=((1,2),(-2,3,4),(-1,-3))
for w in range(16):
    if first_bad(F,w) is None:
        for x in range(16):
            r=(x^w).bit_count()
            assert walk(F,x,repair(F,x,w,r))
for x in range(16):
    for ds in product(range(3),repeat=3):
        assert not walk(((1,),(-1,)),x,ds)

def success_budget(n,t,kappa):
    from math import comb
    d3=3**t
    s=(d3-1).bit_length()+16
    h=[1]+[0]*max(n+1,t+1)
    for j in range(1,t+1):
        h=[3**j]+[h[d-1]+2*h[d+1] for d in range(1,len(h)-1)]+[0]
    num=sum(comb(n,d)*h[d] for d in range(n+1))*((1<<s)//d3)
    den=1<<(n+s)
    # At kappa=128, 89 exceeds 128 log_e(2); kappa always suffices otherwise.
    factor=89 if kappa==128 else kappa
    return (factor*den+num-1)//num,s,d3

def enc(n,g,bit,t,kappa,getbits):
    F=extract(n,g)
    if F is None:return bool(bit and any(eval_g(n,g,x) for x in range(1<<n)))
    trials,s,m=success_budget(n,t,kappa)
    limit=((1<<s)//m)*m
    for _ in range(trials):
        x=getbits(n);u=getbits(s)
        if u>=limit:continue
        u%=m
        ds=[]
        for _ in range(t):u,d=divmod(u,3);ds.append(d)
        if walk(F,x,ds):return bool(bit)
    return False

assert success_budget(128,165,128)[0]==1021393308818026961
for b in (False,True):
    assert not enc(1,[(0,0)],b,1,4,rr.getrandbits)
    assert enc(1,[],b,1,4,lambda bits:0)==b
class AIG:
    def __init__(self,inputs):
        self.base=inputs+1
        self.ops={}
        self.reverse={}
    def both(self,a,b):
        if -1 in (a,b) or a==-b:return -1
        if a==1:return b
        if b==1 or a==b:return a
        pair=tuple(sorted((a,b)))
        if pair not in self.reverse:
            idx=self.base+len(self.ops)+1
            self.ops[idx]=pair;self.reverse[pair]=idx
        return self.reverse[pair]
    def either(self,a,b):return -self.both(-a,-b)
    def any(self,vs):
        if not vs:return -1
        while len(vs)>1:
            vs=[self.either(vs[i],vs[i+1]) if i+1<len(vs) else vs[i]
                for i in range(0,len(vs),2)]
        return vs[0]
    def xor(self,a,b):return self.either(self.both(a,-b),self.both(-a,b))
    def failed(self,F,x):
        return [-self.any([x[abs(v)-1] if v>0 else -x[-v-1] for v in row]) for row in F]
    def first(self,bad):
        m=1<<(len(bad)-1).bit_length()
        tree=[-1]*m+bad+[-1]*(m-len(bad))
        for i in reversed(range(1,m)):tree[i]=self.either(tree[2*i],tree[2*i+1])
        enable=[-1]*(2*m)
        enable[1]=1
        for i in range(1,m):
            enable[2*i]=enable[i]
            enable[2*i+1]=self.both(enable[i],-tree[2*i])
        return [self.both(enable[m+i],f) for i,f in enumerate(bad)]
    def first_shallow(self,bad):
        pref=bad.copy()
        step=1
        while step<len(pref):
            for start in range(0,len(pref),2*step):
                middle=start+step
                if middle<len(pref):
                    left=pref[middle-1]
                    for i in range(middle,min(middle+step,len(pref))):
                        pref[i]=self.either(left,pref[i])
            step*=2
        return [bad[0]]+[self.both(bad[i],-pref[i-1]) for i in range(1,len(bad))]
    def lower(self,out):
        live={abs(out)}
        for g,(a,b) in reversed(self.ops.items()):
            if g in live:live.update((abs(a),abs(b)))
        # Physical NAND outputs implement the negative polarity of each AIG AND.
        literal={1:0,**{i:i-1 for i in range(2,self.base+1)}}
        gates=[]
        depth=[0]*self.base
        def nand(a,b):
            gates.append((a,b));depth.append(max(depth[a],depth[b])+1);return len(depth)-1
        def use(v):
            if v not in literal:literal[v]=nand(literal[-v],literal[-v])
            return literal[v]
        for g,(a,b) in self.ops.items():
            if g in live:literal[-g]=nand(use(a),use(b))
        output=use(out)
        return gates,output,depth[output]

def policy(F,initial,r,n,shallow=False):
    A=AIG(2*r)
    xs=[1 if initial>>i&1 else -1 for i in range(n)]
    valid=1
    for j in range(r):
        lo,hi=2+2*j,3+2*j
        digit=[A.both(-lo,-hi),A.both(lo,-hi),A.both(-lo,hi)]
        valid=A.both(valid,-A.both(lo,hi))
        select=(A.first_shallow if shallow else A.first)(A.failed(F,xs))
        groups=[[[] for _ in range(3)] for _ in xs]
        for row,h in zip(F,select):
            for k in range(3):groups[abs(row[k%len(row)])-1][k].append(h)
        xs=[A.xor(v,A.any([A.both(d,A.any(ids)) for d,ids in zip(digit,parts)]))
            for v,parts in zip(xs,groups)]
    return A.lower(A.both(valid,-A.any(A.failed(F,xs))))

def run_gate(g,out,z,n):
    w=[1]+[z>>i&1 for i in range(n)]
    for a,b in g:w.append(1-(w[a]&w[b]))
    return w[out]

def policy_test():
    rr=Random(851)
    n=128;w=rr.getrandbits(n);cs=[]
    for _ in range(300):
        vs=rr.sample(range(1,n+1),3)
        row=[v if rr.randrange(2) else -v for v in vs]
        if first_bad([row],w) is not None:row[0]*=-1
        cs.append(row)
    F=extract(n,raw_cnf(n,cs,4096))
    # One actual 38-trit certificate, with 11 fixed trits evaluated outside the key policy.
    shifts=[rr.getrandbits(128) for _ in range(190490)]
    j,idx,path=encode(F,w,shifts,38,16,[0,65535],128)
    x=shifts[j]^sum((65535 if i else 0)<<(16*k) for k,i in enumerate(idx))
    for d in path[:11]:
        row=first_bad(F,x)
        if row is None:break
        x ^= 1<<(abs(row[d%len(row)])-1)
    g,out,depth=policy(F,x,27,128)
    ds=path[11:]
    print('chosen shift',j)
    for digs in [ds]+[[rr.randrange(3) for _ in range(27)] for _ in range(20)]:
        z=sum(v<<(2*i) for i,v in enumerate(digs))
        assert run_gate(g,out,z,54)==walk(F,x,digs)
    assert run_gate(g,out,sum(v<<(2*i) for i,v in enumerate(ds)),54)
    assert not run_gate(g,out,3,54)
    print('27-trit policy',len(g),'NANDs, depth',depth)
    g,out,depth=policy(F,x,27,128,shallow=True)
    for digs in [ds]+[[rr.randrange(3) for _ in range(27)] for _ in range(20)]:
        z=sum(v<<(2*i) for i,v in enumerate(digs))
        assert run_gate(g,out,z,54)==walk(F,x,digs)
    print('parallel-prefix policy',len(g),'NANDs, depth',depth)
    # Fair comparator: compile the same exact CNF with half the source inputs hardwired.
    A=AIG(64)
    xs=[1 if w>>i&1 else -1 for i in range(64)]+list(range(2,66))
    g,out,depth=A.lower(-A.any(A.failed(F,xs)))
    assert run_gate(g,out,w>>64,64)
    print('raw balanced-split policy',len(g),'NANDs, depth',depth)
policy_test()
~~~
