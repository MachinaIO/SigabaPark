---
title: Legal-row sign branching with disclosed differences, exact leaf distance and a reversible cancellation on a unique NAND circuit
refs: [definition:WE_CircuitSAT_Capped, theorem:AdvancedEncryption.WE.LegalBranch.SelectSign, theorem:AdvancedEncryption.WE.LegalBranch.LeafLine, theorem:AdvancedEncryption.WE.LegalBranch.FiberCoin, theorem:AdvancedEncryption.WE.LegalBranch.FoldPayload, theorem:AdvancedEncryption.WE.LegalBranch.LeafTransfer, theorem:AdvancedEncryption.WE.LegalBranch.BoundaryMass, theorem:AdvancedEncryption.WE.LegalBranch.FullViewCount]
tags: [witness-encryption, branching-programs, fourier-analysis, circuit-sat]
---

## One selected path per sample

Work over F2. A raw mask U consists of an independent anchor bit and one independent uniform three-bit mask per NAND gate. Write T={(x,y,1+xy)}. The linear wiring map E takes a common anchor a, primary bits and nonterminal gate outputs, repeats ports according to the circuit, uses a at true/default reads and the terminal output, and includes a as the standalone raw anchor. Let W=im E. A raw vector in W with standalone coordinate one and every triple in T is precisely an accepting wired trace; redundant unused primary coordinates can represent the same trace. Publish Q=E^T U, so every W-character is available by parity evaluation. The extra raw anchor prevents homogeneous assignments with a=0 from qualifying.

At a node processing a previously unused gate g choose two distinct legal rows a_g,b_g; choose successor states for the two cases. Write h_g=(a_g+b_g)·U_g and accumulate the sign of a_g·U_g. The scalar recurrence in signs is

    F=((s_a+s_b)/2)F_left+((s_a-s_b)/2)F_right.

It evaluates just the h_g branch times s_a and is always a sign if its leaves are signs. Multiply by the standalone anchor sign. The body is this resulting bit XOR the payload. All gates are visited once per path; a deterministic reordering, even a reordering depending on the already sampled decisions, is allowed. While states may inspect public constraints repeatedly, they never consume a second independent pair on an already processed raw port. Independent public initial coins can initialize the state.

For a prescribed trace frequency r and a fixed order, let f_j(v) be its suffix coefficient starting at state v. With state transitions l(v),r'(v), its coordinate update is (f_{j+1}(l)+f_{j+1}(r'))/2 when the trace uses a_g, (f_{j+1}(l)-f_{j+1}(r'))/2 at b_g, zero otherwise. A terminal constant sign initializes the recursion. This is a sparse signed matrix with at most two entries per state row (add entries at coincident successors). For a terminal sign depending on the whole path, keep the needed history in the state. Sampling a path does not require building the full transfer matrix. SelectSign and LeafTransfer verify the two identities.

## A complete law even when every path difference is exposed

Publish the differences h_g along the path, in addition to Q and the marked body. For a fixed public initial coin and path h, the restrictions on U are exactly d_g·U_g=h_g, where d_g=a_g+b_g in its own raw block. These constraints are independent because each d_g is nonzero in a fresh block. The path has probability 2^-G, and the conditional mask is uniform on that affine subspace. Set D_h=span{d_g} and t_h=(1,a_1,...,a_G) in raw address order. Any odd message-sensitive raw character of the disclosed view has support in the union of t_h+D_h: expand each fixed path indicator as a product of the two-term parity indicators, then multiply by its base sign. This still holds for any postprocessing of the public path, or any chosen terminal sign that is a function of h. Every word in t_h+D_h has a legal row at every gate. The support claim applies to the raw marked sign together with the path; passing to Q retains only wired sensitive frequencies.

If (t_h+D_h)∩W is empty, t_h is outside W+D_h. Binary elimination gives a kernel direction k annihilating W and D_h with t_h·k=1. Translating U by k preserves every bit of Q and the path and swaps the marked sign. FiberCoin and FullViewCount verify the algebraic invariance and finite fiber counting step. If the intersection contains E(v), write E(v)=t_h+Σ c_g d_g. Then its parity on U is v·Q and the base sign is recovered by the XOR of v·Q and Σ c_g h_g. LeafLine verifies the row interpolation. For that path the two message distributions have disjoint supports. Thus the exposed complete-packet total variation is **exactly** the probability of a nonempty intersection. On every false circuit it is zero, including under joint readings, alternate internal marginals, or quantum processing of the classical packet. A supplied witness gives a zero-error read if its rows belong to the selected pairs, otherwise an explicit erasure. Independently repeating R times gives all-erasure probability (1-p_w)^R. The criterion can also be solved by public linear algebra: a successful leaf yields an accepting trace, even without a witness. This qualifies the meaning of any high-bias instance.

## A wiring-directed schedule and exact replay

Start with the affine system on all primary and internal bits with the terminal pinned to one. At each gate project the current system onto its three port bits and intersect with the four legal rows. If there are one or two points, retain all. If there are three or four, partition into the first two and the remainder in the public ordering 00,01,10,11, selecting the side with the previous gate's fair h (use an independent public first bit). Complete a singleton by a legal row outside the entire current projection's *legal intersection*. For an empty intersection continue with any two legal rows; imposing them makes the system inconsistent. Add two independent equations specifying the retained binary line. Preserve the inconsistent state if reached. Gates may be handled in reverse topological order, exploiting the terminal pin. Only previous split decisions affect which future branches really need a random guess; a new gate difference is fresh. At a final live leaf the accumulated affine system describes exactly its accepted traces. Distinct nonempty split halves cover all original trace possibilities. One fixed witness reaches its compatible leaf with probability 2^-k, where k is the number of actual splits on that route. Repeated gates under fanout can be forced by the same earlier split. This is an exact affine-branching SAT procedure as well as an issuer.

For g0=NAND(x,x), g1=NAND(x,y), g2=NAND(g1,g1) use order 0,1,2. The unique witness is (1,1). The two g1 states select (00,01) or (10,11); all four rows really occur in the schedule. g0 is semantically unused by the final output but its raw mask supplies the route; its repeated x input is wired. On all 2048 full tapes the exposed whole-packet distance is 1/2, while the same sampler hiding the path has distance **zero** by cancellation. In order 2,1,0 the terminal pin forces g1=0 and then x=y=1, giving exposed distance one. For the false three-gate circuit !x, NAND(!x,x), NOT of that NAND, exact exposed distance is zero. The code below groups whole ciphertexts rather than just the intended witness projection.

The hidden version can align signs on a unique accepting trace. On a live leaf solve the public affine system and choose a deterministic representative v*. Multiply the terminal sign by (-1)^(Σ c_g(v*)h_g); on dead leaves leave it unchanged. This is a function of the path and preserves legal support. For a unique trace v, all live leaves choose v and the corrected base sign equals its wired parity. Dead leaves contribute zero at this frequency by the kernel translation. All other wired odd coefficients vanish. In particular on an injectively represented unique trace, Q is uniform on its image and the unique bias has magnitude p_live; the two complete hidden views have exactly this distance. Equivalently condition the signed conditional bias on Q and apply binary Fourier inversion on its image. The three-gate enumeration gives exactly 1/2 after alignment with no path published. With several traces the representative can change and this one-frequency conclusion need not hold.

A larger replay chooses a 128-bit target, computes all 128 negations, conjoins the corresponding literals, pads with default-true NANDs to exactly 4096 gates and forces the final output. Reverse order makes every required AND input and then every primary known; unused padding is deterministic. All split counts are zero and the unique trace is recovered without looping through its 2^128 possibilities. The script verified one full tape in 0.0247 s of Python wall time on the research host. The generic raw issuer uses 12289 fair mask bits plus the initial routing bit. For a direct dense Q it writes 4224 wiring bits, one marked bit, the initial bit and 4096 path bits (8322 bits before framing); unused or linearly dependent emissions can be removed. Sparse data structures, system elimination, conditional branches and the cost of writing a Machine program remain outside this timing. Public SAT propagation itself suffices for this family.

## Forward compression and its limitation

In the alternate forward schedule start on all n input bits. Keep each computed wire affine on the current fiber. Parent rank at most one gives at most two reachable rows and an affine output. If the two parents have independent linear parts, use the previous fresh difference (or an initial fair bit at the first gate) to guess the left parent, reduce dimension by one, then proceed with its two possible rows. Only the k actual rank-two decisions need be made public. For a final fiber of dimension n-k, the row-choice correction J(w)=Σ c_g(w)h_g is affine there: each c_g(w) is constant or one affine selector. Thus the issuer can disclose J by at most n-k+1 coefficients instead of printing G differences. For each fixed path the gate masks and projection Q are exactly as in the raw issuer; this is a coarsening of that view.

More strongly, compute the affine expression in the free variables obtained by adding the body, J(w), and Q evaluated on the forward trace with its **last output replaced by one**. Real minus pinned trace differs only at the final output port, so the result is β+(1+C_leaf(w))r, where r is the final output-port mask. FoldPayload verifies the bit cancellation. That mask is fresh independently of all k routing decisions: no decision uses the final gate's h. Store the normalized affine expression together with the k decisions in at most n+1 total bits (or its coordinates in the actual basis of span{1,C_leaf}, of dimension at most two). These statements assume at least one gate, and deterministic public coordinate/basis conventions. An accepting witness in the chosen fiber always reads its bit. On a fully rejecting fiber the value is one independent fair constant. On every fiber containing a solution, the exposed bit is recoverable by solving the public affine output. Thus this direct compressed issuer has exact whole-packet distance p_live.

In a star using x as the common left parent in many gates NAND(x,y_j), one guess of x suffices to make every such gate affine in its remaining parent; the cost in split probability need not be a direct product over its fanout. For the general *forward*, unpruned rule, live leaf mass lies between the raw accepting density and twice that density: the public guesses choose each affine cell proportionally to its cardinality, and its Boolean affine terminal value accepts either all or exactly half of a live cell. BoundaryMass checks the mass inequality. A unique witness among 128 inputs therefore gives at most 2^-127 here. The reverse propagation starting from the terminal condition has a different distribution over final cells and escapes this particular estimate. No all-circuit bound on the number of surviving or forced decisions, security reduction to a lattice assumption, or capped WE machine is established. These effects concern the present adaptive signed compiler. No hardness premise is introduced.

## Reproduction

```python
from itertools import product
from collections import Counter
from random import Random
from time import perf_counter

T=(4,6,5,3)
def parity(x): return x.bit_count()%2
def var(i): return 2<<i

class System:
    def __init__(self): self.b={}; self.live=True
    def reduce(self,e):
        v=e&1; e &= ~1
        while e:
            j=e.bit_length()-1
            if j in self.b: e ^= self.b[j]
            else: v ^= 1<<j; e ^= 1<<j
        return v
    def add(self,e):
        e=self.reduce(e)
        if e<2: self.live &= not e
        else: self.b[e.bit_length()-1]=e

def legal(sys,ports):
    if not sys.live: return []
    forms=[sys.reduce(e) for e in ports]
    ans=[]
    for r in T:
        tmp=System()
        for j,d in enumerate(forms): tmp.add(d^(r>>j&1))
        if tmp.live: ans.append(r)
    return ans

def bind(sys,ports,a,b):
    pivot=(a^b)&-(a^b)
    for j,d in enumerate(ports):
        if (1<<j)==pivot: continue
        f=d^(a>>j&1)
        if (a^b)>>j&1:
            i=pivot.bit_length()-1; f ^= ports[i]^(a>>i&1)
        sys.add(f)

def issue(n,gates,order,beta,raw,h,align=False):
    order=tuple(order)
    # Positive integer bits denote wires; bit zero denotes a constant one.
    sys=System(); sys.add(var(n+len(gates)-1)^1)
    base=raw&1; raw >>= 1; Q=base; H=[]; splits=0; choices={}
    first=h
    for g in order:
        x,y=gates[g]; z=var(n+g); ports=(x,y,z)
        L=legal(sys,ports)
        if len(L)>2:
            splits+=1
            # T is ordered in left-parent halves (00,01) then (10,11).
            co=L[:2] if not h else L[2:]
        else: co=L
        if not co: a,b=T[:2]
        else:
            a=co[0]
            b=co[1] if len(co)>1 else next(r for r in T if r not in L)
        choices[g]=(a,b)
        U=(raw>>(3*g))&7
        h=parity((a^b)&U); H.append(h)
        base ^= parity(a&U)
        for j,d in enumerate((x,y,1 if g==len(gates)-1 else z)):
            if U>>j&1: Q ^= d
        bind(sys,ports,a,b)
    if align and sys.live:
        for g,hg in zip(order,H):
            ports=(*gates[g],var(n+g))
            row=sum((sys.reduce(p)&1)<<j for j,p in enumerate(ports))
            a,b=choices[g]
            assert row in (a,b)
            base ^= int(row==b)*hg
    return (Q,first,tuple(H),base^beta), bool(sys.live),splits,choices

def exact(n,gates,order):
    N=1<<(2+3*len(gates)); hist=[Counter(),Counter()]; wins=0; projections=set()
    for z in range(N):
        p,win,_,c=issue(n,gates,order,0,z>>1,z&1);wins+=win
        hist[0][p]+=1;hist[1][p[:-1]+(1^p[-1],)]+=1
        projections.add(c.get(1))
    diff=sum(abs(hist[0][p]-hist[1][p]) for p in hist[0]|hist[1])
    assert diff==2*wins
    return wins,N,projections

def comparator(target):
    n=len(target); gs=[(var(i),var(i)) for i in range(n)]
    lits=[var(i) if b else var(i+n) for i,b in enumerate(target)]
    cur=lits[0]
    for e in lits[1:]:
        if e==lits[-1]:
            while len(gs)<4094: gs.append((1,1))
        gs.append((cur,e)); t=var(n+len(gs)-1);gs.append((t,t));cur=var(n+len(gs)-1)
    return gs

if __name__=='__main__':
    x,y=var(0),var(1); z=var(2); u=var(3)
    g=[(x,x),(x,y),(u,u)] # Only x=y=1 accepts.
    print('unique forward',exact(2,g,range(3)))
    for align in (False,True):
        hists=[Counter(),Counter()]
        for z in range(2048):
            (q,_,_,b),*_=issue(2,g,(0,1,2),0,z>>1,z&1,align)
            hists[0][q,b]+=1;hists[1][q,1^b]+=1
        diff=sum(abs(hists[0][p]-hists[1][p]) for p in hists[0]|hists[1])
        assert diff==(2048 if align else 0)
        print('hidden alignment',align,diff,'/4096')
    print('unique reverse',exact(2,g,(2,1,0)))
    # g0=!x; g1=NAND(!x,x)=1; g2=!g1=0
    g=[(x,x),(var(1),x),(var(2),var(2))]
    print('false',exact(1,g,(0,1,2)))
    t=[int(i%3!=0) for i in range(128)]; g=comparator(t);rng=Random(250)
    a=perf_counter();p,win,splits,_=issue(128,g,reversed(range(len(g))),0,rng.getrandbits(1+3*len(g)),1);tm=perf_counter()-a
    assert len(g)==4096 and win and splits==0
    print('padded 128 unique',len(g),win,splits,round(tm,4),'s (Python, one sample)')
```
