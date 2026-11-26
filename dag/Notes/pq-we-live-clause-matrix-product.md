---
title: Read-once matrix programs for circuit witnesses with reusable clause coordinates
refs: [definition:WE_CircuitSAT, note:pq-we-ggh15-chain-verdict, theorem:AdvancedEncryption.WE.MatrixChain.terminal_box_count]
tags: [witness-encryption, branching-programs, complexity, lwe]
---

For a NAND circuit, encode the satisfying computation as a binary matrix product with one level per used trace bit. This gives a polynomial honest-algorithm alternative to split tables on arbitrary input circuits. The cryptographic backend in this note is the published CVW/VWW construction, under its additional assumptions. The contribution here is a different matrix program for its frontend, with a polynomial-time compiler and an executable comparison to the diagonal CNF program of Construction 6.2. This supplies an efficiency benchmark for the open security problem in this DAG. [Vaikuntanathan, Wee and Wichs, Sections 4–6](https://eprint.iacr.org/2022/1140.pdf).

**From the original witness to a single path.** Give every NAND output a trace bit z. Add (a or z), (b or z), (not a or not b or not z) and require the final gate output to be true when a gate exists (the empty gate list returns true). Substitute true for zero and unavailable reads according to the wire semantics. The constraints force z=NAND(a,b). Induction over gates proves that a satisfying assignment is exactly an accepting trace and the supplied witness extends to it by one ordinary circuit evaluation. Deduplicate clauses and remove tautologies. A permutation of the trace variables is public and independent of the message. The listing uses consecutive labels for clarity; remove unused inputs and compact their indices for an encoding with large sparse input labels. Include the cost of reading the statement and witness in the machine clock.

**Reusing coordinates.** For the chosen variable order let c be the number of distinct non-tautological clauses including any empty clause. Assign each nonsingleton clause the closed interval between its first and last variable. Let L be the maximum number of overlapping such intervals. Use width w=L+3. Color intervals greedily in start order, reusing an index only after the previous interval ends. Three permanent coordinates carry a source of value one, a count of already falsified clauses, and the message bit. Initialize the failure count by the empty clause indicator. At the first variable, send the source to the new clause slot if the selected bit leaves its literal false. At intermediate levels keep its slot unless the assignment satisfies a literal. At its last variable send the surviving slot to the failure counter if that last literal also fails. Singletons failing at the current bit use a single source-to-counter edge; duplicate removal ensures at most one such singleton per bit and level. Keep the counter and message by identity edges. Project the last layer to counter and message by deleting its other output columns. The zero-variable case uses one fixed dummy transition.

Induction after every level gives each open slot the indicator that no literal seen so far satisfies the clause, and gives the accumulator the number of completely falsified clauses. Thus the terminal row is (0,f,mu,0,...) with 0<=f<=c. The original u and all matrices are binary. No step enumerates assignments, finds a witness or tests satisfiability. A simple dense compiler costs O(H w² + poly(statement length)) bit entries/elementary operations, allowing the polynomial cost of sorting and bookkeeping separately, for H=max(1,number of trace variables). One may compile the diagonal baseline as well and use the smaller width, giving w<=min(c+1,L+3) on nonempty ordinary formulas (use the original message convention for that fallback).

**Modulus.** VWW Lemma 5.3 uses uniformity of a linear combination of uniform rows. A positive failure count can be a nonunit over a power of two. For the count backend choose a prime p>max(c,2) by sieving up to twice max(c+1,3) and take q=p^k in the required bit-length regime, rounding the logarithm up by less than log2(p). The encryption assumptions must hold at this modulus and all the widths and noise parameters must be chosen with slack. Every prefix before the final projection has source coefficient one. On a false statement every full path has a unit failure coefficient. For a valid path with message one the message coefficient is a unit. Hence these linear maps onto each scalar output are surjective. Intermediate magnitudes are polynomial: any subpath can create at most one new failure per clause from a unit source, and a slot can contribute at most one to the sink. The additional polynomial norm factor is absorbed in the noise-flooding slack. The secret message and initialization vector are supplied to the encoder; only the encrypted program and message-independent layout are sent.

**Three polynomial bounds.** Take the paper's tensor encoder with lattice dimension n, matrix column count m=O(n w log q), and a root block with n rows. It emits two root blocks and 2(H-1) integer matrices of size m by m. Encoding entries as residues suffices for evaluation modulo q, using the centered final product and the scheme's shortness test; equivalently, use bounded Gaussian integer encodings with overwhelming tail slack. The former gives at most (2nm+2(H-1)m²) ceil(log2 q) bits plus public framing. Honest Enc calls polynomial-time TrapGen once per level and at most 2(H-1)m column samplers, plus dense polynomial-sized matrix products. For example forming each (M tensor S)A costs O((nw)² m) ring operations, before trapdoor work. Use the finite precision and tail cutoffs of a bounded implementation if claiming worst-case machine time. Dec first computes the trace and then multiplies an n by m matrix by H-1 selected m by m matrices, using O(H n m²) modular multiply-adds after lookup, plus linear scanning/decoding of the ciphertext and the shortness check. The circuit description can be included in public framing when Dec does not receive it separately. Schoolbook modular arithmetic is polynomial in log q. With fixed subexponential-hardness exponent delta>0, Remark 5.1 takes n polynomial in H and lambda and log q polynomial as well; enlarging the internal security parameter by a polynomial including the statement length covers width and slack. All three quantities are polynomial jointly in the statement length and unary security parameter. This statement concerns honest algorithms. The published security reduction can be superpolynomial and uses evasive LWE in addition to subexponentially hard LWE. Its PPT formulation would need appropriate quantum hardness and a quantum-valid reduction for a PQ theorem. The DAG's ordinary LWE registry does not discharge this assumption.

**Checks.** The listing constructs the actual sparse binary transition matrices. It compares every row output against a direct clause evaluator and checks that every accepting NAND trace is forced. It includes empty, contradictory, duplicate, tautological and singleton clauses, either message, and out-of-range reads. Sliding three-literal clauses on 32, 128 and 512 variables give diagonal widths 31, 127 and 511 and interval width 6 in all cases, with the same number of levels as variables. These examples have simple public SAT witnesses. They measure the representation cost only. A second control compiles 4096 NAND gates in both input-first and interleaved variable orders. Actual lattice encryption at the resulting parameters and a machine-level PQ reduction remain open.

On that 128-input control the circuit-to-trace reduction has 4224 levels. The ordinary diagonal program has width 9601, input-first interval allocation gives 2821, and a schedule reading each input immediately before its 32-gate segment gives 28. Order selection is a public deterministic compiler option; no optimization of pathwidth is required. A change in width alone does not certify a measured ciphertext speedup.

An exact decision shortcut uses the same compiled edges with message zero. Keep the set of reachable live-slot masks and prune transitions entering the failure counter, since its value never decreases. Bitwise OR computes the supports of nonnegative integer row updates. Two equal retained masks have identical possible continuations. After the last projection, the zero mask is reachable exactly on YES instances. With a polynomial cap B, stop before storing more than B+1 masks; a timeout gives no verdict. A completed run encrypts a bit as its AND with the decision, with constant decryption work and identical ciphertext distributions on NO. The cap makes the attempt polynomial even on failure, e.g. O(H B w²) edge visits plus polynomial bitset and dictionary costs (a sorted deterministic dictionary suffices). In the 4096-gate ordered control the cap H completed at peak four masks and 25,022 attempted transitions. This shortcut covers a certified subclass unconditionally. The count backend keeps the honest algorithms polynomial on all other instances, conditionally on its cryptographic security assumptions. The shortcut uses no encrypted matrix sampler.

**One root row and a short final block.** There is a further backend change independent of the clause layout. Encrypt the same program, retaining only row 1 of each of the two root blocks and the first t columns of each final block. When H=1 apply both restrictions to the root. For H>=2 this transmits 2m+2(H-2)m²+2mt residues, and for H=1 it transmits 2t. Dec multiplies one row through the chosen blocks and tests its t centered entries, outputting zero if all are short. For H>=2 its dense arithmetic is O((H-2)m²+mt), plus reading the statement, deriving the trace and accessing the selected blocks. The computational message-security reduction is deterministic ciphertext postprocessing on both distributions. The correctness of this particular shorter test requires a separate argument.

Write B for the bound on the absolute centered evaluation error from VWW Lemma 4.3; choose parameters with q>=16(B+1). Use q=p^k as above, let rho<1 upper-bound the largest atom modulo p of one entry of the iid tensor factors S_i,b, and let eta be the total variation of the final trapdoor public matrix from uniform. For a fixed valid witness path and message one, its logical message coordinate is one. Start with the first standard row and multiply by the selected S matrices modulo p. Given a surviving row, each coordinate of its next product vanishes with probability at most rho: condition on all entries of that column except one having nonzero row coefficient. Columns are independent. Thus the chance of losing the row in any of the H factors is at most H rho^n. A fixed nondegenerate constant-width discrete Gaussian has positive constant masses at both zero and one, distinct modulo p, so a uniform rho<1 exists. Condition on the tensor factors. On survival the ideal terminal coefficient row has a unit modulo p^k. The final A_H is independent of these factors, and after its eta switch to uniform each of its first t columns gives an independent uniform ideal output. If the observed entry has centered size <=B and its error has size <=B, the ideal entry lies in the centered interval of radius 2B. Its probability is at most (4B+1)/q. No independence from the evaluation error is needed. For message zero the valid logical row is zero, so the shortness bound suffices. With evaluation-error probability epsilon, the per-witness bit-one failure is at most

    epsilon + H rho^n + eta + ((4B+1)/q)^t.

The accompanying finite-ring theorem gives the exact box cardinality for a unit pivot and arbitrary offsets depending on all the remaining coordinates. More generally, a target terminal error 2^-lambda only needs t=ceil(lambda/log2(q/(4B+1))). When q >= (4B+1) 2^lambda, one terminal column suffices; this trades modulus headroom for smaller ciphertext and sampler counts. Check the ratio with the recomputed B, m and lattice hardness at the chosen parameters. At H=2, one root row and one terminal column require 4m residues and a single length-m dot product. For the conservative fixed-ratio setting use t=ceil(lambda)+1, m>=t, and n with H rho^n negligible. For simultaneous correctness across every path, add H bits to the terminal repetition budget and set the other failure bounds with the corresponding margin; the standard per-witness claim already follows without that union bound. For H=1 the same argument uses A_1. Direct Enc only needs the selected root row and t target columns and t column-preimage draws per final branch, using independent per-column sampling with the shared trapdoor. All interior blocks remain full width. Enc can still use the original TrapGen for the final public matrix and discard its unused columns. These savings are exact dimensional and operation-count changes; no end-to-end lattice performance measurement is claimed. The second listing checks equality of the truncated and full products, the small-field row survival bound and exact uniformity for unit rows over two prime powers.

~~~python
"""Binary matrix products for a CNF in a fixed variable order."""
from random import Random
from itertools import product

def compile_program(clauses, h, message):
    # Remove duplicate literals, tautologies and duplicate clauses. Rank literals 1..h.
    cs = {tuple(sorted(set(c))) for c in clauses if not any(-v in c for v in c)}
    if any(v==0 or abs(v)>h for c in cs for v in c):
        raise ValueError('invalid literal')
    empty = int(() in cs)
    cs.discard(())
    starts = [[] for _ in range(h+1)]
    for c in sorted(cs):
        first, last = min(map(abs,c)), max(map(abs,c))
        starts[first].append((last, frozenset(c)))
    # Reserve source, cumulative failures and message; color closed intervals.
    # Separate singleton clauses by sign: at most one can fail per layer.
    live = {}
    startvec = [1,empty,message]
    width = 3
    layers = []
    for i in range(1,h+1):
        new = starts[i]
        free = [j for j in range(3,width) if j not in live]
        for last,c in new:
            if last==i:continue
            if free:slot=free.pop()
            else:slot=width;width+=1
            live[slot] = (last,c,i)
        branches = []
        for bit in (0,1):
            lit=i if bit else -i
            edges={(0,0),(1,1),(2,2)}
            if any(last==i and lit not in c for last,c in new):edges.add((0,1))
            for slot,(last,c,first) in live.items():
                if lit not in c:
                    edges.add((0 if i==first else slot,1 if i==last else slot))
            branches.append(edges)
        layers.append(branches)
        live={j:rec for j,rec in live.items() if rec[0]>i}
    # Project at the last layer by deleting outgoing coordinates other than the outputs.
    if layers:
        layers[-1]=[{(s,t) for s,t in branch if t in (1,2)} for branch in layers[-1]]
    else:
        layers.append([{(1,1),(2,2)}]*2)
    return startvec+[0]*(width-3),layers

def eval_program(program,bits):
    row,layers=program
    for i,b in enumerate(tuple(bits) or (0,)):
        out=[0]*len(row)
        for s,t in layers[i][b]:out[t]+=row[s]
        row=out
    return row

def nand_cnf(n,gates):
    # Wire zero and reads of unavailable wires mean true.
    clauses=[]
    for j,(a,b) in enumerate(gates,n+1):
        a=a if 0<a<j else 0;b=b if 0<b<j else 0
        for u in (a,b):
            if u:clauses.append((u,j))
        clauses.append(tuple(x for x in (-a,-b,-j) if x))
    if gates:clauses.append((n+len(gates),))
    return clauses

def run_tests():
    rng=Random(1107);tests=0
    assert all(nand_cnf(n,[])==[] for n in (0,1,128))
    for h in range(0,8):
        for case in range(25):
            cs=[tuple(rng.choice((-1,1))*rng.randint(1,h) for _ in range(rng.randrange(1,5))) if h else () for _ in range(rng.randrange(1,12))]
            if case%4==0:cs.append(())
            distinct={frozenset(c) for c in cs if not any(-v in c for v in c)}
            for msg in (0,1):
                prog=compile_program(cs,h,msg)
                if msg==0:
                    expected=any(all(any(bits[abs(v)-1]==(v>0) for v in c) for c in distinct) for bits in product((0,1),repeat=h))
                    assert decide_capped(prog,1<<h)[0]==expected
                for bits in product((0,1),repeat=h):
                    num=sum(not any(bits[abs(v)-1]==(v>0) for v in c) for c in distinct)
                    row=eval_program(prog,bits)
                    assert row[1]==num and row[2]==msg and sum(row)==num+msg
                    tests+=1
    for n in range(1,5):
        for _ in range(24):
            gates=[tuple(rng.randrange(n+i+3) for _ in range(2)) for i in range(4)]
            cs=nand_cnf(n,gates);pr=compile_program(cs,n+4,0)
            for bits in product((0,1),repeat=n):
                trace=[1,*bits]
                for a,b in gates:
                    trace.append(1-(trace[a] if a<len(trace) else 1)*(trace[b] if b<len(trace) else 1))
                for g in product((0,1),repeat=4):
                    accepts=not any(eval_program(pr,bits+g))
                    assert accepts==(tuple(trace[n+1:])==g and trace[-1]==1)
                    tests+=1
    print('complete row and trace checks',tests)
    for h in (32,128,512):
        cs=[(i,-(i+1),i+2) for i in range(1,h-1)]
        pr=compile_program(cs,h,0)
        print('variables, original width, compiled width, levels',h,len(cs)+1,len(pr[0]),len(pr[1]))
def decide_capped(pr, cap):
    # Message zero. Once a prefix violates a closed clause it can never accept.
    initial,layers=pr
    if initial[1]:return False,0,0
    states={1};peak=1;transitions=0
    for level in layers:
        nxt=set()
        for mask in states:
            for edges in level:
                transitions+=1;out=0
                for src,dst in edges:
                    if mask>>src&1:out|=1<<dst
                if out&2:continue
                nxt.add(out)
                if len(nxt)>cap:return None,max(peak,len(nxt)),transitions
        states=nxt;peak=max(peak,len(states))
        if not states:break
    return 0 in states,peak,transitions

def stream_control():
    n=128
    # Each new input is consumed by one 32-NAND segment. Wire 0 is true.
    gates=[];prev=0;order=[]
    for i in range(1,n+1):
        order.append(i)
        for step in range(32):
            gates.append((prev,i if step%3==0 else prev))
            prev=n+len(gates);order.append(prev)
    cs=nand_cnf(n,gates)
    rank={v:i for i,v in enumerate(order,1)}
    perm=[tuple((1 if v>0 else -1)*rank[abs(v)] for v in c) for c in cs]
    H=len(order)
    raw=len({frozenset(c) for c in cs if not any(-v in c for v in c)})+1
    a=compile_program(cs,H,0);b=compile_program(perm,H,0)
    print('capped exact SAT (result, peak live states, transitions)',decide_capped(b,H))
    rng=Random(222)
    for _ in range(20):
        trace=[1]+[rng.randrange(2) for _ in range(n)]
        for i,j in gates:trace.append(1-trace[i]*trace[j])
        for pos in [None,rng.randrange(n+1,H+1)]:
            vals=trace.copy()
            if pos:vals[pos]^=1
            assert eval_program(a,vals[1:])[1]==eval_program(b,[vals[v] for v in order])[1]
            assert (not eval_program(b,[vals[v] for v in order])[1])==(pos is None and bool(trace[-1]))
    print('4096 NANDs: levels / diagonal / original-order frontier / interleaved frontier',H,raw,len(a[0]),len(b[0]))
if __name__=='__main__':run_tests();stream_control()
~~~

~~~python
"""Endpoint truncation checks. Standard library, exact integer arithmetic."""
from itertools import product
from fractions import Fraction
from random import Random
from math import gcd

def mul(a,b,q):
    return [[sum(x*y for x,y in zip(r,c))%q for c in zip(*b)] for r in a]

def check():
    rng=Random(921);chains=0
    for q in (9,25,343,65537):
        for H in (1,2,3,5):
            for root,m,t in ((1,3,2),(4,7,3),(3,4,4)):
                gen=lambda n,k:[[rng.randrange(q) for _ in range(k)] for _ in range(n)]
                ct=[[gen(root if i==0 else m,m) for b in range(2)] for i in range(H)]
                for path in product(range(2),repeat=H):
                    full=ct[0][path[0]]
                    cut=[full[0]]
                    if H==1:cut=[cut[0][:t]]
                    for i,b in enumerate(path[1:],1):
                        full=mul(full,ct[i][b],q)
                        block=ct[i][b] if i+1<H else [r[:t] for r in ct[i][b]]
                        cut=mul(cut,block,q)
                    assert cut[0]==full[0][:t]
                    chains+=1
    cases=0
    for p,q in ((3,9),(5,25)):
        for r in product(range(p),repeat=2):
            if r==(0,0):continue
            zero=sum((r[0]*i+r[1]*j)%p==0 for i,j in product((-1,0,1),repeat=2))
            assert Fraction(zero,9)<=Fraction(1,3)
            assert Fraction(zero**2,81)<=Fraction(1,9)
            hits=[0]*q
            for c in product(range(q),repeat=2):hits[sum(i*j for i,j in zip(r,c))%q]+=1
            assert hits==[q]*q
            cases+=1
    print(chains,'matrix paths;',cases,'prime-power row distributions')
if __name__=='__main__':check()
~~~

The third listing runs both shortened encryption and decryption for a two-input NAND using NumPy. Extract the first listing as frontend.py and this listing as toy.py, then run OPENBLAS_NUM_THREADS=1 python toy.py frontend.py. It constructs gadget trapdoors, samples short preimages by randomized nearest-plane sampling, checks every preimage congruence, sends one root row and two terminal columns, and evaluates every path with modular integer arithmetic. Its small setup, floating Gaussian decisions, deterministic test RNG, uniform final matrix, and observed error threshold are for a correctness diagnostic only. In particular the diagnostic computes a bound from private sampled norms to check the estimates; a WE decoder must instead use a public parameter bound as above.

With the same seed at lattice dimensions 2 and 4, all 32 path residuals satisfied their bounds. At dimension 2 five of six valid decryptions passed. The missed bit-one path lost its tensor row modulo 7. At dimension 4 all six passed; each ciphertext used 303416 residues and Enc sampled 780 preimage columns. At that same m=388 the full three-level dense layout has 605280 residues (2*4*388+4*388²) and 1552 preimage columns. This directly exercises the survival term in the correctness estimate and shows why one successful small instance would not suffice to set security parameters.

~~~python
"""Toy lattice chain. Integer congruences checked exactly, floating Gaussian sampler."""
from itertools import product
import numpy as np
from math import ceil,exp,pi,log
from random import Random

def toy(front,n):
    rng=Random(6091);q=7**45;rad=256;k=ceil(q.bit_length()/8)
    cs=front['nand_cnf'](2,[(1,2)])
    def arr(r,c,f):return np.array([[f() for _ in range(c)] for _ in range(r)],dtype=object)
    def digits(z):
        z=z.copy()%q;rows=[]
        for _ in range(k):rows.append(z%rad);z=z//rad
        assert not z.any()
        return np.stack(rows,axis=1).reshape((-1,z.shape[1]))
    def gauss(center,width):
        lo=int(np.floor(center-12*width));hi=int(np.ceil(center+12*width))
        while True:
            j=rng.randint(lo,hi)
            if rng.random()<exp(-pi*((j-center)/width)**2):return j
    u0,l0=front['compile_program'](cs,3,0)
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
                centers[:j+1]+=np.outer(tri[:j+1,j],z)
                y+=np.outer(basis[:,j],np.array(z,dtype=object))
            assert not ((A@y-target)%q).any()
            return y
        return A,preimages
    valid=0;checks=0;fail=[]
    for bit in (0,1):
        u,layers=front['compile_program'](cs,3,bit)
        ct=[];logical=[];maxerr=0;maxS=0;maxD=0;samplers=0;t=2
        for i,choices in enumerate(layers):
            final=i==len(layers)-1
            if final:
                # Uniform final matrix in the statistically switched experiment.
                A=arr(d,t,lambda:rng.randrange(q));next_pre=None
            else:A,next_pre=trap()
            pair=[];plain=[]
            for edges in choices:
                M=np.zeros((w,w),dtype=object)
                for s,j in edges:M[s,j]=1
                S=arr(n,n,lambda:gauss(0,2.5));maxS=max(maxS,max(map(abs,S.flat)))
                F=np.kron(np.array([u],dtype=object)@M,S)[:1] if not i else np.kron(M,S)
                E=arr(F.shape[0],A.shape[1],lambda:gauss(0,2))
                maxerr=max(maxerr,max(map(abs,E.flat)))
                Z=(F@A+E)%q
                if i:
                    D=pre(Z);samplers+=Z.shape[1]
                    maxD=max(maxD,max(map(abs,D.flat)));pair.append(D)
                else:pair.append(Z)
                plain.append(F)
            ct.append(pair);logical.append(plain);pre=next_pre
        B=maxerr
        for _ in layers[1:]:
            B=m*maxD*B+d*(len(cs)+1)*(n*max(1,maxS))**len(layers)*maxerr
        assert 16*(B+1)<q
        for path in product(range(2),repeat=3):
            y=ct[0][path[0]];F=logical[0][path[0]]
            for i,b in enumerate(path[1:],1):y=(y@ct[i][b])%q;F=F@logical[i][b]
            center=lambda a:(a+q//2)%q-q//2
            assert max(map(abs,center(y-F@A).flat))<=B;checks+=1
            if path[2]==1 and not(path[0] and path[1]):
                decoded=int(max(map(abs,center(y).flat))>B)
                if decoded!=bit:fail.append((path,not (F%7).any()))
                valid+=1
        print('message, levels, width, m, residues, preimage columns, B bits:',
              bit,len(layers),w,m,sum(c.size for pair in ct for c in pair),samplers,int(B).bit_length())
    print('dimension',n,'exact residuals',checks,'correct valid decryptions',valid-len(fail),'of',valid,'failures (path, vanished mod 7)',fail)
    return fail
if __name__=='__main__':
    import sys,runpy
    front=runpy.run_path(sys.argv[1]);toy(front,2)
    assert not toy(front,4)
~~~
