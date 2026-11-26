---
title: Replace layered ABE by public prefix reachability and a single terminal ABE split
refs: [definition:WE_CircuitSAT, note:pq-we-split-witness-abe, note:we-circuitsat-live-wire-baseline, theorem:AdvancedEncryption.WE.XWE.folded_cut_exact, theorem:AdvancedEncryption.WE.XWE.folded_cut_frontier]
tags: [witness-encryption, attribute-based-encryption, circuit-sat]
---

The layered ABE chain in PR #80 enumerates a prefix block, internal (block,state) pairs and a terminal block. For the registered ordinary WE primitive, the circuit and transition functions are public. This permits computing reachable states in the clear and using just one final ABE setup. Repartition the **remaining suffix bits together with the reachable state**, rather than stopping at a table of whole suffixes. This gives a different resource frontier. The underlying split-witness ABE compiler is from [Non-Trivial Witness Encryption and Null-iO](https://eprint.iacr.org/2017/874.pdf), specialized in the DAG's split-witness note.

**Construction.** Starting at the initial public state, replace R at each public prefix layer by the distinct h(r,w) over r in R and block values w. Each value is attainable because successive witness blocks are independent. The Lean theorem folded_cut_exact proves the exact path characterization for any finite transition alphabet at each layer. At the cut let R have D elements, with a t-bit unread suffix and predicate Q. The resulting verifier has domain R times the suffix alphabet. Every original witness computes a reachable state by running its prefix; every accepted pair extends to a full witness by the path characterization. Extractable WE is not asserted.

For a pure split with a bits of suffix on the key side, publish one KP-ABE key for each (r,u) in R times the a-bit prefixes. Its predicate on the other t-a bits v is Q(r,u||v). Publish one encryption of the same bit for each v under the same fresh master setup. The numbers of keys and ciphertexts are D·2^a and 2^(t-a), respectively. State r is hardwired directly into the key's predicate. No exponentially large state-index lookup circuit is needed in that predicate. A decryptor computes its state, selects the proper published key and ciphertext, and uses ABE decryption. For a false instance all issued predicates reject all published attributes. Ordinary collusion-secure selective-attribute ABE with quantum security suffices conditionally, with the single-challenge entry fixed before setup and all other entries generated under the challenge public key. The reduction must pay for the public reachability computation, queries, companion entries, and key/attribute indexing. The only message-switch hybrids are on the last ciphertext table. There are no encrypted next-layer keys. This is not a proved quantitative instantiation under the registered LWE function.

One can transpose a Cartesian split by hardwiring the other coordinate in the keys and publishing ciphertexts for just the realized labels of the first coordinate. In particular one can place D raw state labels on the ciphertext side and the entire suffix on the key side. Under the squared-advantage budget of #64 this orientation contributes 2 log2 D bits of loss before reduction overhead, while it may make the key table and policies costly. Alternatively rank all D·2^t valid pairs and tile the ranks into K rows and L columns, rejecting the padded end. This gives nearly equal integer table sizes, but if the row and column both participate in decoding the state index the policy must implement a public state dictionary or exploit its structure. The exponent proof below uses the pure split.

**Exact exponent model.** Let there be one initial public prefix block, j internal public prefix blocks, and one terminal suffix. Public state width is at most s at the chosen boundaries, and e≥s. The initial block can consume a≤e bits, and each of the j others can consume up to e-s bits at at most 2^e public transition evaluations per layer. A suffix of t bits fits terminal tables of at most 2^e each whenever s+t≤2e: put max(0,t-e) suffix bits with the state in the keys. Both tables then fit. In the uniform worst-capacity model these constraints exactly cover m bits iff

    m + (j+1)s ≤ (j+3)e.

This follows by filling the three capacities e, j(e-s), 2e-s, as proved by folded_cut_frontier. Any total between zero and j(e-s) can be distributed over j capped blocks by greedy filling. Empty blocks are allowed in this numerical model. An actual verifier must support the chosen boundaries and widths; a width guarantee at just one set of boundaries cannot be moved by arithmetic. Tightness is for the displayed caps, not a lower bound for all circuits. The exponents count transitions and table entries; one public transition, one ABE key and one ciphertext can have very different costs.

For 128 bits, j=2 and s=16, the four-stage chain in #80 has best displayed exponent 40. The public-prefix construction reaches exponent 36 if those widths are available at suitable splits (35 fails since 128+48>175). Use prefix block sizes 36,20,20 and suffix size 52. At most 3·2^36 public transition evaluations suffice for the prefix. Hardwire the state and 18 suffix bits in each key, leaving 34 attribute bits. This uses at most 2^34 keys and exactly 2^34 ciphertexts. The pre-overhead single-challenge security budget in #64 is then 128+2·34=196 bits. If forced to retain #80's example of balanced boundaries 40,24,24,40, the public work cap stays at exponent 40; one still gets two terminal tables of at most 2^28 entries by assigning 12 suffix bits to the keys. For a public streamed verifier that remains narrow through the entire suffix, direct reachability all the way to the output is also available and may be cheaper. No general exponent-36 claim for 128-input NAND lists follows.

**Obtaining a sound cut from a raw NAND list.** The implementation normalizes default-true forward reads and prunes gates outside the output cone. It introduces each live input bit at first use, computes a NAND and projects to wires with future reads, deduplicating states. Stop at a specified gate boundary. The resulting states are the exact projected assignments on the live cut, and the only unread input bits required by the residual gate list are independent of that state. The suffix uses the stored actual wire values. The first-use invariant of the live-wire baseline establishes this at each gate. A cap is checked before allocating a new state expansion; on overflow this candidate cut is unavailable and the original split (#64) remains available. Finding an optimal boundary, implementing key generation and bounding the clock on the registered unary input remain open.

**128 inputs and 4,096 gates.** The first 112 bits drive a one-hot counter mod 7, then 16 suffix bits are tested against a fixed tag. The SAT instance also requires counter state 3; the UNSAT instance requires both states 2 and 3. The generic compiler receives the raw NANDs and the gate boundary immediately after the counter. It discovers that the SAT tail reads only one counter lane, and the UNSAT tail only two. It certifies two and three cut labels, respectively. A chunked source-level implementation retaining all seven labels would have 458,752 terminal pairs.

| Generic cut | Public prefix candidate transitions | Cut states | Residual NANDs | Terminal pairs | Keys × ciphertexts in balanced padded tiling | Accepting cells |
|---|---:|---:|---:|---:|---:|---:|
| SAT | 31,879 | 2 | 42 | 131,072 | 362 × 363 | 1 |
| UNSAT | 32,161 | 3 | 44 | 196,608 | 443 × 444 | 0 |

The cell counts were checked by running the actual residual evaluator over the entire rectangle. Running public reachability all the way to the output uses 32,137 and 32,550 candidate transitions respectively (about 0.04–0.05 s in local Python), and already decides both cases. These controls justify selecting the direct one-bit encryptor here. They do not benchmark ABE. The Lean proofs certify finite reachability and the aggregate numerical frontier; the generic Python circuit-cut implementation is differential-tested at every cut on all 625 two-input two-gate circuits and 100 further seeded circuits. The security reduction and registered machine-level submission remain open.

~~~python
from math import isqrt
from random import Random
from time import perf_counter

def circuit(no):
    g=[]
    def nand(a,b):
        g.append((a,b))
        return 128+len(g)
    def both(a,b):
        c=nand(a,b)
        return nand(c,c)
    false=nand(0,0)
    st=[0]+[false]*6
    for w in range(1,113):
        nw=nand(w,w)
        st=[nand(nand(nw,st[i]),nand(w,st[(i-1)%7])) for i in range(7)]
    tag=0x6a35
    eq=0
    for j in range(16):
        w=113+j
        eq=both(eq,w if tag>>j&1 else nand(w,w))
    accept=both(st[2],st[3]) if no else st[3]
    while len(g)<4094:nand(0,0)
    both(accept,eq)
    assert len(g)==4096
    return g

def ev(g,x):
    w=[1]+[x>>i&1 for i in range(128)]
    for a,b in g:w.append(1-(w[a]&w[b]))
    return w[-1]

# Enumerate prefix transitions independently of all suffix attributes.
states={0}
transitions=0
for _ in range(112):
    transitions+=2*len(states)
    states={(s+b)%7 for s in states for b in range(2)}
assert states==set(range(7))
# Certify the transition symbolically on the reachable one-hot domain.
for s in states:
    for b in range(2):
        new=[int(((not b) and i==s) or (b and (i-1)%7==s)) for i in range(7)]
        assert new==[int(i==(s+b)%7) for i in range(7)]
R=sorted(states)
B=1<<16
N=len(R)*B
L=isqrt(N-1)+1
K=(N+L-1)//L
print('prefix transitions, states, terminal pairs, balanced rows and columns:',transitions,len(R),N,K,L)

def q(s,v,no):return v==0x6a35 and (s==2 and s==3 if no else s==3)
def policy(i,j,no):
    z=i*L+j
    return z<N and q(R[z//B],z%B,no)
rng=Random(82)
for no in (False,True):
    g=circuit(no)
    assert ev(g,(7|(0x6a35<<112)))==int(not no)
    for _ in range(300):
        x=rng.getrandbits(112)
        y=rng.choice((rng.randrange(B),0x6a35))
        i,j=divmod((x.bit_count()%7)*B+y,L)
        assert ev(g,x|(y<<112))==policy(i,j,no)
    t=perf_counter()
    hits=sum(policy(i,j,no) for i in range(K) for j in range(L))
    assert hits==int(not no)
    print(no,'accepting cells',hits,'pad',K*L-N,'seconds',round(perf_counter()-t,4))

from itertools import product
class Cut:
    def __init__(self,n,g,cut,cap):
        self.out=n+len(g) if g else 0
        gates={}
        for j,(a,b) in enumerate(g):
            v=n+1+j
            gates[v]=(a if a<v else 0,b if b<v else 0)
        used={self.out}
        for v in reversed(gates):
            if v in used:used.update(gates[v])
        gates={v:p for v,p in gates.items() if v in used}
        last={}
        for v,p in gates.items():
            for w in p:last[w]=v
        last[self.out]=n+len(g)+1
        live=()
        states={()}
        self.steps=0
        self.prefix=[]
        for v,(a,b) in gates.items():
            if v>n+cut:break
            fresh=tuple(sorted({w for w in (a,b) if 0<w<=n and w not in live}))
            after=tuple(w for w in (*live,*fresh,v) if last.get(w,0)>v)
            self.prefix.append((v,a,b))
            if len(states)*(1<<len(fresh))>cap:raise OverflowError
            new=set()
            for st in states:
                for bits in product(range(2),repeat=len(fresh)):
                    w={0:1,**dict(zip(live,st)),**dict(zip(fresh,bits))}
                    w[v]=1-(w[a]&w[b])
                    new.add(tuple(w[i] for i in after))
                    self.steps+=1
            states=new
            live=after
        self.live=live
        self.states=sorted(states)
        self.index={s:i for i,s in enumerate(self.states)}
        self.tail=[(v,a,b) for v,(a,b) in gates.items() if v>n+cut]
        self.fresh=sorted({w for _,a,b in self.tail for w in (a,b) if 0<w<=n and w not in live})
        self.B=1<<len(self.fresh)
        self.N=len(states)*self.B
        self.L=isqrt(self.N-1)+1

    def locate(self,n,x):
        w={0:1,**{i+1:x>>i&1 for i in range(n)}}
        for v,a,b in self.prefix:w[v]=1-(w[a]&w[b])
        r=self.index[tuple(w[i] for i in self.live)]
        y=sum(w[i]<<j for j,i in enumerate(self.fresh))
        return divmod(r*self.B+y,self.L)

    def cell(self,i,j):
        z=i*self.L+j
        if z>=self.N:return False
        idx,y=divmod(z,self.B)
        w={0:1,**dict(zip(self.live,self.states[idx]))}
        w.update({v:y>>j&1 for j,v in enumerate(self.fresh)})
        for v,a,b in self.tail:w[v]=1-(w[a]&w[b])
        return bool(w[self.out])

def original(n,g,x):
    w=[1]+[x>>i&1 for i in range(n)]
    for a,b in g:w.append(1-((w[a] if a<len(w) else 1)&(w[b] if b<len(w) else 1)))
    return w[-1] if g else 1

def small(n,g):
    for c in range(len(g)+1):
        cut=Cut(n,g,c,1024)
        vals={cut.locate(n,x) for x in range(1<<n)}
        assert len(vals)==cut.N
        for x in range(1<<n):
            assert cut.cell(*cut.locate(n,x))==original(n,g,x)
        for z in range(cut.N,((cut.N+cut.L-1)//cut.L)*cut.L):
            assert not cut.cell(*divmod(z,cut.L))
for a,b,c,d in product(range(5),repeat=4):small(2,[(a,b),(c,d)])
for _ in range(100):
    n=rng.randrange(6);s=rng.randrange(10)
    small(n,[(rng.randrange(n+s+1),rng.randrange(n+s+1)) for _ in range(s)])
for no in (False,True):
    g=circuit(no)
    cut=Cut(128,g,1+112*22,1024)
    for _ in range(100):
        x=rng.getrandbits(112)|(rng.choice((rng.randrange(B),0x6a35))<<112)
        assert cut.cell(*cut.locate(128,x))==ev(g,x)
    assert cut.cell(*cut.locate(128,7|(0x6a35<<112)))!=no
    print('generic',no,len(cut.live),len(cut.states),len(cut.fresh),len(cut.tail),cut.steps,cut.N)
    t=perf_counter()
    rows=(cut.N+cut.L-1)//cut.L
    hits=sum(cut.cell(i,j) for i in range(rows) for j in range(cut.L))
    assert hits==int(not no)
    print('NAND tail scan',rows,cut.L,hits,round(perf_counter()-t,3))
    t=perf_counter()
    end=Cut(128,g,len(g),1024)
    direct=any(end.cell(*divmod(z,end.L)) for z in range(end.N))
    assert direct!=no
    print('public scan to output',end.steps,round(perf_counter()-t,3))
~~~
