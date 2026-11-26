---
title: Read-once matrix programs for circuit witnesses with reusable clause coordinates
refs: [definition:WE_CircuitSAT, note:pq-we-ggh15-chain-verdict]
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
