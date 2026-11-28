---
title: Pointwise cut certificates, a deterministic coefficient witness, and batched witness trials
refs: [definition:WE_CircuitSAT_Capped, definition:DensityTrials, theorem:AdvancedEncryption.WE.DensityTrials.minimum_weight, theorem:AdvancedEncryption.WE.DensityTrials.batch_lane, theorem:AdvancedEncryption.WE.DensityTrials.fair_error_count, theorem:AdvancedEncryption.WE.DensityTrials.trial_bound, theorem:AdvancedEncryption.WE.DensityTrials.minimal_coefficient]
tags: [witness-encryption, circuit-sat, reed-muller, multitape-machines]
---

For a bounded public cut we give two ways to detect a positive output. The first uses point-specific low-degree polynomials to certify a lower bound on witness density. The second extracts a witness from the coefficients themselves and can decide the covered circuit deterministically. A 4096-gate fixture demonstrates both. For black-box trials, packing 306 candidates into parallel Boolean columns and grouping 32 gates at a time gives a data-tape traversal ledger of at most 403,767,321 bit-cell units on every registered topology. This is a partial ledger, not a canonical machine cost.

### Checking a cut and its density

Normalize a reference to wire 0 whenever it is not earlier than the current output wire. Wire 0 is true. Maintain the live frontier backwards from the final gate. When its width is within a public cap k, consider that subset of wires as a candidate cut. Limit the number of candidates and per-wire ANF work with public bounds. Failure to find a suitable cut returns unknown. For a proposed cut, compute the truth table g on k formal variables by overriding those wire values, retaining unknown for any unbound primary input. Compute the actual Boolean ANFs F_i of the boundary values from the public circuit. On NAND multiply sparse polynomials with squarefree monomials, XOR cancelling duplicate terms and toggle the constant. Abort uncertified wires when an operation exceeds its cap. A known suffix table and exact boundary polynomials then give g(F(x)) on every physical witness x. No independence or surjectivity of the F_i is assumed. Exact global boundary functions matter: substituting one-sided indicator lower bounds into arbitrary cut polynomials is unsound.

Let M index cut monomials of weighted degree at most d, using the actual ANF degrees of F_i as weights. Let v(z) give their evaluations at formal cut value z. Let O be the binary row span of v(z) over all g(z)=0. For each g(z)=1 require v(z) outside O. Equivalently binary elimination produces a coefficient vector c_z that annihilates every rejecting row and evaluates to one at z; one vector need not work at all accepting z simultaneously. The listing constructs and checks these certificates. If x is a witness, Q(u)=c_{F(x)}·v(F(u)) is nonzero at x, vanishes wherever the source rejects, and has physical multilinear degree at most d. In particular, the circuit has either no witnesses or density at least 2^-d. Exhaustive checking on formal rows includes unreachable rows and may reject a useful certificate; acceptance is sufficient.

The Lean minimum-weight theorem uses full binary tables, weight equal to the positive leaf count, and degree by the recursion f(x,t)=a(x)+t(a(x)+b(x)). This recursion gives precisely multilinear degree at most d by comparing monomials containing the last variable. When the two halves coincide, double the induction bound on one half. Otherwise the nonzero difference has degree at most d−1 and its weight is at most the sum of the two weights. The resulting integer inequality is 2^n ≤ weight(f)·2^d. The equivalence between this recursive degree and sparse ANF substitution is mathematical; the program-to-Lean refinement remains open.

### A direct deterministic decoder for the same certificate

Compute each composed feature in v(F(x)) once. For each physical squarefree monomial indexed by a subset S of input variables, collect its coefficients across those features into a vector D_S. Then v(F(1_S)) is the sum of D_U over U contained in S. If every D_S belongs to O then v(F(x)) belongs to O for every x. Under coverage of all accepting rows this proves UNSAT, even if the public suffix table has positive rows unreachable from the physical input.

Otherwise choose an S of minimum cardinality with D_S outside O. Every strict subset contributes an element of O, so v(F(1_S)) lies outside O. Hence 1_S is a satisfying *original* witness of weight at most d. This YES test works even if some other accepting rows were not covered. Lean proves the minimal-coefficient argument for every additive subgroup, by subtracting the sum over the proper subsets. The algorithm needs one witness evaluation for replay, no enumeration of the whole 2^|S| subcube. If coverage fails and every coefficient is inside O, return unknown.

When eight cut variables are affine and d=2 there are at most 37 admitted features if none is constant (fold constants first), and at most 1+128+8128=8257 physical monomials. There are at most 28 products of two affine functions, each with at most 129² term pairs. The input-dependent prefix ANFs may be much more expensive to obtain; the cap is essential. The registered test fixture has eight neighboring input XORs as its designated cut and an OR of two independent-on-formal-input quadratic predicates below it. The smallest tested positive/negative certificate degrees are 2/4. The live-frontier search also found a width-two cut giving an actual witness of weight one. On two identical boundary functions and a suffix demanding unequal bits the method certifies NO. On a cubic conjunction with d=2 it returns unknown. Another 512 small tests checked the decisions with dependent quadratic boundaries against enumeration.

### Public sampling, structure and exact errors

With a density certificate, draw T independent uniform witnesses as *fresh Enc coins*. Enc outputs the message if any accepts. On a miss it outputs an independent fair bit; Dec simply reads the ciphertext bit. On every false instance the output is uniform regardless of the message. On a positive instance with w witnesses out of N=2^128, the error for either fixed message and every valid witness equals (N−w)^T/(2N^T). The cardinality proof identifies each error-producing (sample tuple, coin) with exactly one tuple of rejecting assignments. The integer threshold (2^d−1)^T·2^127 ≤ (2^d)^T suffices for error at most 2^-128. The exact smallest T at d=1,2,3,4 is 127,306,660,1364. An erasure or fixed bit on failure needs 128,309,665,1375 in the worst message case. A codimension-d affine flat attains the minimum density. For a conjunction selecting one particular 128-bit word, the miss probability is (1−2^-128)^T; a density-based correctness claim at d=2 fails on this circuit.

The deterministic Hamming ball of radius d hits every nonzero degree-d ANF: take an inclusion-minimal nonzero coefficient. Its size at degree two on 128 variables is 8257, or 301 in 24 known independent coordinates. The latter gives zero miss with fewer points than the 306 IID trials, if the circuit is correctly parameterized by those 24 coordinates. A universal deterministic evaluation-only family needs at least the dimension of the promised polynomial space, since a smaller evaluation map has a nonzero kernel. This dimension lower bound is for all polynomials of the stated degree, not for a particular registered gate-size subclass. For a random affine cube of dimension k use independent uniform directions, allowing degeneracy. Its all-miss probability for rejection indicator h is at least (E h)^(2^k). To see this, define h_a(x)=h(x)h(x+a), apply the dimension-(k−1) statement conditional on a, and use Jensen and E_a E_x h_a=(Eh)^2. For a codimension-two accepting flat the exact all-miss probabilities for k=2,3 are 21/64 and 45/256; IID gives 81/256 and 6561/65536. Conditioning on linearly independent directions changes a probability by at most the probability that the original directions were dependent, bounded by (2^k−1)/2^128. This correction cannot reverse these concrete gaps. No advantage improvement follows from using cube inputs here.

### Batched sequential tape design

A wire holds the T bits for that wire across candidates, in a fixed lane order. The Lean fold proves that every lane equals SigabaNeo.evalGates on its own input for any gate list, including self and forward references. To realize bounded blocks, split the 4096 normalized gates into 128 packets of 32. At packet start with f prior columns gather the e≤64 distinct external wires in descending address order in one backward trip over the history and one return. Internal references become local indices following the gathered columns; forward references are replaced by zero *before* classification. The local array never exceeds e+32≤96 columns. For each gate sweep out and back through the local history once to collect both operands, emit their bitwise NAND to the global and local histories, then rewind local storage after the packet. Repeated references may be collected together. Induction on the position in the packet identifies every local array element with its global column; the packed evaluator agrees with the lane fold. The schedule uses public gate addresses only.

Use (T+1) data cells per column including a separator; keep indexing metadata on separate tapes in this ledger. A conservative data-head budget in column units is n+3 for initialization and a final scan, and per packet of length b:
    
    2f + 4e + (e+b) + sum_{i=0}^{b−1} (2(e+i)+16).

The terms pay for the global sweep and return, gathered-column copies including orientation, local reset, and gate-local sweeps and staging. One staging implementation copies a reversed column into a scratch buffer then reads it backwards to recover increasing lane order; it rewinds the buffer per column. For a gate use a private buffer for each operand, collect both on the local sweep, rewind, read them in the same lane order while appending to the two output histories, and reset. Four additional traversals per gathered column and sixteen per gate allow these copies, scratch rewinds and output writes. The formula deliberately sums data-head movements that could overlap in a multitape transition. It omits control work when data heads do not scan a data cell. Initialization draws 128T independent bits and stores the true column; a separate fair coin is needed for the miss bit.

On every registered graph the multiplier is at most 1,315,203. For T=306,309,660,1364,2773 the resulting data-cell bounds are 403,767,321; 407,712,930; 869,349,183; 1,795,252,095; 3,648,373,122. Four 4096-gate fixtures at 306 lanes were checked on every lane against scalar evaluation, and all 256 legal one-input/two-gate topologies were checked at both block sizes. The random fixture reached the 96-column peak. The earlier one-witness trace component costs 484,601,619 including its canonical description; it produces a private framed trace and charges repeated addressing on one assignment. Multiplying its cost by T would pay for a different interface and would fail to exploit column sharing.

The registered unary statement itself can have up to 103,821,312 bits before outer framing. Count parser traversal, unary-to-binary conversion (13-bit normalized addresses), sorting and remapping ≤64 distinct references, counters/delimiters, table padding, paired input/output frames, random instructions and all stationary control steps. For example binary carry updates over an address of length a need fewer than 2a changes plus initialization/reset, but this alone is not a decoder clock. Both clock maxima and both descriptions are charged; a machine with k work tapes and z states has a canonical zero-oracle description length 6z·3^k·(4+4k+Nat.size z). The ledger does not assign a tape or state count or claim that data travels plus a nominal overhead proves a strict 2^32 time-plus-description bound. No full capped machine, or quantum-security theorem, is supplied.

On a publicly verified dense or deterministically decided instance one can select the corresponding method. Otherwise an existing full WE on the unchanged original statement, using its ciphertext verbatim, would give an exact fallback branch even with the registered challenge containing the statement. On this branch both the attacker and the challenge stay unchanged. Both algorithms must agree on any public branch choice if decoding depends on it, and the worst-case costs include preprocessing and the backend. A trial-only scheme with a fair miss bit has unconditional hiding on all NO instances but lacks correctness on sparse YES instances. This work does not supply the missing budgeted general backend.

### Reproducible Python checks

```python
"""Private independent trial coins. The bit masks below represent T physical tape cells."""
from itertools import combinations, product
from math import comb
from random import Random

def norm(n,gates):
    return [tuple(a if a < n+1+j else 0 for a in g) for j,g in enumerate(gates)]

def batch(n,gates,cols,t,block):
    full=(1<<t)-1
    hist=[full]+list(cols)
    peak=0
    movement=n+3  # initialize n+1 columns and scan the final one with return
    for start in range(0,len(gates),block):
        base=len(hist)
        packet=[tuple(a if a < base+j else 0 for a in g)
                for j,g in enumerate(gates[start:start+block])]
        requested=sorted({a for g in packet for a in g if a<base},reverse=True)
        ext={a:i for i,a in enumerate(requested)}
        def slot(a):
            return ext[a] if a<base else len(ext)+a-base
        plan=[tuple(slot(a) for a in g) for g in packet]
        local=[]
        # One trip from the end of history to zero and back.
        for address in range(base-1,-1,-1):
            if len(local)<len(requested) and address==requested[len(local)]:
                local.append(hist[address])
        assert len(local)==len(ext)
        movement+=2*base+4*len(ext)
        for a,b in plan:
            # One reverse scan over all local columns collects both operands.
            u=v=None
            for j in range(len(local)-1,-1,-1):
                if j==a:u=local[j]
                if j==b:v=local[j]
            z=full^(u&v)
            movement+=2*len(local)+16
            local.append(z)
            hist.append(z)
        movement+=len(local)  # rewind local tape for reuse at the next block
        peak=max(peak,len(local))
    return (hist[-1] if gates else full),movement*(t+1),peak

def scalar(n,gates,w):
    H=[1]+[(w>>j)&1 for j in range(n)]
    for l,r in gates:
        H.append(1^((H[l] if l<len(H) else 1)&(H[r] if r<len(H) else 1)))
    return H[-1] if gates else 1

def boundary(n,gates,cut,cap=4096):
    """Verify exact ANF of each selected boundary wire and exact suffix table from raw gates."""
    gs=norm(n,gates)
    width=1<<len(cut)
    full=(1<<width)-1
    override={a:sum(((x>>i)&1)<<x for x in range(width)) for i,a in enumerate(cut)}
    # Position in the actual shared gate list. None means the expression is uncertified.
    anf=[{0}]+[{1<<i} for i in range(n)]
    table=[override.get(i,full if i==0 else None) for i in range(n+1)]
    for j,(a,b) in enumerate(gs):
        l,r=anf[a],anf[b]
        out=None
        if l is not None and r is not None and len(l)*len(r)<=cap:
            out={0}
            for m in l:
                for k in r:
                    q=m|k
                    if q in out:out.remove(q)
                    else:out.add(q)
            if len(out)>cap:out=None
        anf.append(out)
        u,v=table[a],table[b]
        table.append(override.get(n+1+j,None if u is None or v is None else full^(u&v)))
    if len(set(cut))!=len(cut) or not all(0<a<len(anf) and anf[a] is not None for a in cut):
        return None
    tb=table[-1] if gates else full
    if tb is None:return None
    return [(tb>>x)&1 for x in range(width)],[anf[a] for a in cut]

def witness_row(equations,unit):
    """Solve f(off)=0 and f(on)=1 by binary elimination, retaining coefficients."""
    piv={}
    for vec,rhs in [(v,0) for v in equations]+[(unit,1)]:
        while vec and (j:=vec.bit_length()-1) in piv:
            v,b=piv[j];vec^=v;rhs^=b
        if vec:piv[vec.bit_length()-1]=vec,rhs
        elif rhs:return None
    coeff=0
    for j,(vec,rhs) in sorted(piv.items()):
        if (vec&coeff).bit_count()%2!=rhs:coeff^=1<<j
    return coeff

def cert(table,forms,d):
    weights=[max((m.bit_count() for m in a),default=0) for a in forms]
    mon=[m for m in range(len(table)) if sum(weights[i] for i in range(len(forms)) if m>>i&1)<=d]
    rows=[sum(int((x&m)==m)<<i for i,m in enumerate(mon)) for x in range(len(table))]
    off=[row for x,row in enumerate(rows) if not table[x]]
    out={}
    for x,v in enumerate(table):
        if v:
            c=witness_row(off,rows[x])
            if c is None:return None
            assert ((c&rows[x]).bit_count()&1) and all((c&u).bit_count()%2==0 for u in off)
            out[x]=[m for i,m in enumerate(mon) if c>>i&1]
    return out

def trial(d,k):
    if d==0:return 1
    q=1<<d;l=0;h=1
    def enough(t):return ((q-1)**t<<k)<=q**t
    while not enough(h):h*=2
    while h-l>1:
        m=(l+h)//2
        if enough(m):h=m
        else:l=m
    return h

def fixture():
    g=[]
    def gate(l,r):
        g.append((l,r));return 128+len(g)
    def X(a,b):
        z=gate(a,b);return gate(gate(a,z),gate(b,z))
    def A(a,b):
        z=gate(a,b);return gate(z,z)
    cut=[X(i+1,i+2) for i in range(8)]
    def q(w):return X(A(w[0],w[1]),A(w[2],w[3]))
    a,b=q(cut[:4]),q(cut[4:])
    gate(gate(a,a),gate(b,b))
    last=g.pop()
    return g+[(4224,4224)]*(4095-len(g))+[last],cut

def ledger(n,s,t,b):
    total=n+3
    for j in range(0,s,b):
        k=min(b,s-j);f=n+1+j;e=min(f,2*k)
        total+=2*f+4*e+e+k+sum(2*(e+i)+16 for i in range(k))
    return (t+1)*total

def run():
    for gates in product(product(range(4),repeat=2),repeat=2):
        for b in (1,2):
            out,_,_=batch(1,gates,[2],2,b)
            assert out==sum(scalar(1,gates,w)<<w for w in range(2))
    rng=Random(160)
    g,cut=fixture()
    tbl,forms=boundary(128,g,cut)
    assert cert(tbl,forms,1) is None and cert(tbl,forms,2) is not None
    assert (cert([1-v for v in tbl],forms,3) is None and
            cert([1-v for v in tbl],forms,4) is not None)
    print('registered two-block quadratic OR: cut degrees 2 and 4')
    for name,gs in [('cut',g),('forward',[(4224,4224)]*4096),
                    ('random',[(rng.randrange(4225),rng.randrange(4225)) for _ in range(4096)]),
                    ('local',[(128+i,128+i) for i in range(4096)])]:
        T=306; ws=[rng.getrandbits(128) for _ in range(T)]
        cols=[sum(((w>>i)&1)<<j for j,w in enumerate(ws)) for i in range(128)]
        out,travel,peak=batch(128,gs,cols,T,32)
        assert out==sum(scalar(128,gs,w)<<j for j,w in enumerate(ws))
        assert peak<=96 and travel<=ledger(128,4096,T,32)
        print(name,'slot peak',peak,'data-cell travel bound',travel)
    print('degrees, ordinary and fair fallback trial counts',
          [(d,trial(d,128),trial(d,127)) for d in range(1,5)])
    print('worst-topology data bounds at block 32',
          [(t,ledger(128,4096,t,32)) for t in (306,309,660,1364,2773)])
    print('rank-24 quadratic hitting family',sum(comb(24,i) for i in range(3)))

def row_basis(vectors):
    piv={}
    for v in vectors:
        v=row_reduce(v,piv)
        if v:piv[v.bit_length()-1]=v
    return piv

def row_reduce(v,piv):
    while v and (j:=v.bit_length()-1) in piv:v ^= piv[j]
    return v

def discover(n,gates,k,d,budget):
    """Deterministic live-prefix cuts. A budget limits checked cuts, not the language."""
    if not gates:return 'yes',0,()
    gs=norm(n,gates)
    live={n+len(gs)}
    tested=0
    for j in range(len(gs)-1,-1,-1):
        h=n+1+j
        if h not in live:continue
        live.remove(h);live.update(a for a in gs[j] if a)
        if len(live)>k:continue
        if tested==budget:break
        tested+=1
        c=tuple(sorted(live))
        model=boundary(n,gs,c)
        if model is None:continue
        result,w=coefficient_decide(*model,d)
        if result!='unknown':
            return result,w,c
    return 'unknown',None,()

def coefficient_decide(table,forms,d):
    weights=[max((m.bit_count() for m in a),default=0) for a in forms]
    mon=[m for m in range(len(table)) if sum(weights[i] for i in range(len(forms)) if m>>i&1)<=d]
    rows=[sum(int((x&m)==m)<<i for i,m in enumerate(mon)) for x in range(len(table))]
    O=row_basis(v for x,v in enumerate(rows) if not table[x])
    covered=all(row_reduce(v,O) for x,v in enumerate(rows) if table[x])
    # Composition of each admitted cut monomial only once. Polynomials are
    # sets of squarefree monomials with coefficient one. Symmetric difference
    # adds coefficients in GF(2).
    cache={0:{0}}
    D={}
    for col,m in enumerate(mon):
        if m:
            low=m&-m
            P=set()
            for a in cache[m^low]:
                for b in forms[low.bit_length()-1]:
                    P.symmetric_difference_update((a|b,))
            cache[m]=P
        for s in cache[m]:
            D[s]=D.get(s,0)^(1<<col)
    for s in sorted(D,key=int.bit_count):
        if row_reduce(D[s],O):
            z=sum((sum((m&s)==m for m in p)%2)<<j for j,p in enumerate(forms))
            assert table[z]
            return 'yes',s
    return ('no' if covered else 'unknown'),None

def coeff_tests():
    g,cut=fixture()
    tab,forms=boundary(128,g,cut)
    ds,dw,dc=discover(128,g,8,2,32)
    assert ds=='yes' and scalar(128,g,dw)
    print('publicly discovered cut width',len(dc),'witness weight',dw.bit_count())
    status,w=coefficient_decide(tab,forms,2)
    assert status=='yes' and w.bit_count()<=2 and scalar(128,g,w)
    # Two identical boundary polynomials never reach unequal formal bits.
    tab=[0,1,1,0]
    assert coefficient_decide(tab,[{1},{1}],1)==('no',None)
    # A nonzero cubic is outside the degree-two scalar-point certificate class.
    assert coefficient_decide([0]*7+[1],[{1},{2},{4}],2)==('unknown',None)
    rng=Random(160)
    for _ in range(128):
        # Dependent quadratic boundaries and a random four-bit public suffix.
        forms=[{m for m in range(16) if m.bit_count()<=2 and rng.randrange(3)==0}
               for _ in range(4)]
        tab=[rng.randrange(2) for _ in range(16)]
        vals=[tab[sum((sum((m&w)==m for m in p)%2)<<j for j,p in enumerate(forms))]
              for w in range(16)]
        for d in (1,2,3,4):
            status,w=coefficient_decide(tab,forms,d)
            assert status!='yes' or vals[w] and w.bit_count()<=d
            assert status!='no' or not any(vals)
            if cert(tab,forms,d) is not None:assert (status=='yes')==bool(any(vals))
    print('coefficient solver: registered YES, dependent-cut NO, uncovered unknown, 512 cross-checks')

if __name__=='__main__':
    run()
    coeff_tests()

```
