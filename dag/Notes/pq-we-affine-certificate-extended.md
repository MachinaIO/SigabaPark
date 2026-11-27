---
title: "Compressing CircuitSAT witnesses before split-witness lattice ABE by linearizing nonlinear gates (extended)"
refs: [definition:WE_CircuitSAT, theorem:AdvancedEncryption.WE.XWE.linearized_certificate]
tags: [witness-encryption, circuit-sat, lattice, preprocessing]
supersedes: pq-we-affine-certificate
---

## A shorter witness with a public verifier

Start with the exact registered NAND evaluator. Translate constants, XORs and complemented wires into affine forms over GF(2). Each surviving nonlinear NAND introduces a fresh coordinate y_i. Both operands are affine forms of x and preceding y coordinates. This is the usual XOR-AND representation with a constant wire; a polynomial-time normalizer can simply leave unrecognized NANDs in the graph. In a 4-NAND XOR diamond reuse the original endpoints; remove dead gates by reverse reachability. Resolve forward references to true at the time of the read.

For every NAND choose an oriented pair (A_i,B_i) whose product equals the original product. Over bits, (a,b), (b,a) and (1+a+b,a) are all valid since a²=a. Orientations are public and may depend on the circuit. Let t be the GF(2) row rank of the linear parts of the selected A_i in the *joint* input and gate-output coordinates. Publish no secret basis. Both algorithms compute the same deterministic echelon basis and coordinates from the statement. The new witness consists of the t evaluations of these basis rows on the original accepting run. Known affine constants are then added back to recover every selected operand z_i. The basis can include internal wires because a decryptor with the original witness can evaluate every gate.

For a trial certificate, the verifier asks for a solution v=(x,y) of three sets of equations:
* A_i(v)=z_i at every selected operand;
* y_i+z_i B_i(v)=1 at every nonlinear gate;
* the affine output equals one.

With fixed z this is one affine consistency check with 2k+1 rows and n+k unknowns for k nonlinear gates. These are the equations of the accompanying Lean theorem specialized to GF(2). Soundness uses the first set of equations: guessing inconsistent selector values cannot make a false circuit pass. Conversely a satisfying execution gives a basis certificate and a solution to all rows. Acyclicity ensures every consistent solution describes a real execution. The executable verifier substitutes the y coordinates in order, then eliminates the remaining input coordinates. Both implementations have polynomial preprocessing and verification time. For example, ordinary bit-level Gaussian elimination on the augmented dense system takes O((n+3k+2)^3) elementary bit operations. This preprocessing does not enumerate the images of either witness half.

## Composition and costs

Use this new predicate as the verifier in the [split-witness lattice ABE construction, Section 3.2](https://eprint.iacr.org/2017/874.pdf). Split its t-bit certificate into halves. The number of issued keys is 2^floor(t/2) and the number of encrypted attributes is 2^ceil(t/2). The ABE policies implement the polynomial-size consistency test. The WE decryptor first converts its original witness into the certificate. Every NO instance has *all* key/attribute pairs unauthorized, and an actual witness selects an authorized pair. If t≥n use the original verifier and witness instead. Mode selection is deterministic from the public statement. For small t another option is to decide SAT outright by enumerating at most 2^t systems and use the assumption-free one-bit baseline. When reporting a speedup one must include the polynomial size/depth of elimination, the revised ABE parameters, and tape costs for both modes. This is an instance-dependent improvement in enumeration counts. The worst-case split exponent for 128 inputs remains 64.

Orientation search need not minimize rank. A reproducible polynomial heuristic visits gates in order, prefers a selector already in the current span, then the candidate whose coefficient row occurs most often across the graph. No certificate of optimality is needed to validate the computed rank. Algebraically the optimization target for a gate with independent operand rows a,b is to intersect the plane span(a,b) in some nonzero vector; this plane has exactly three nonzero vectors over GF(2). All planes must be hit by one low-dimensional subspace. Greedy failure to find such a subspace does not rule it out.

## A 128-input control and scope

The code below builds a circuit with 4096 gates and 16 disjoint eight-input groups. For each group q is the parity of its first four bits and s_0,s_1 are the two pair parities of the remaining four. Its two nonlinear products are s_i(s_i+q). XOR of all 32 complemented products gives the output. Every input is essential: each group contributes (1+q)(s_0+s_1) and the other groups can be set to zero. Choosing the difference orientation makes both selectors in a group share the same coefficient row. Independent groups give t=16 at k=32. The balanced construction issues **256 keys and 256 attribute ciphertexts** for this instance. The full uncompressed split gives 2^64 of each. A 65,536-certificate exhaustive check found exactly one infeasible certificate. This is a deliberately structured example and its explicit formula also makes SAT easy. The numbers measure table entries and soundness of the certificate transformation, not elapsed ABE time.

A separate check compared existential certificate verification with direct SAT on all 625 two-input two-gate registered circuits and 300 seeded circuits. For every accepting assignment it also tested the actual witness conversion. The Lean proof checks the joint range-membership equivalence, assuming that the coordinate decoder recovers the chosen measurements. The Python code exercises the gate translator, orientation search and elimination. A formal refinement of those routines, an implementation of the resulting ABE policy with concrete LWE parameters, and a bound for hard circuit families remain open.

~~~python
from itertools import product
from random import Random

def compile_net(n, gates):
    # Each reference is constant 0 or 1, a primary input, or a node index.
    nodes = [('const', 0, 0), ('const', 1, 1)] + [('input', i, i) for i in range(n)]
    wires = [1] + list(range(2, n+2))
    for a, b in gates:
        u, v = (wires[j] if j < len(wires) else 1 for j in (a, b))
        kind, left, right = 'nand', u, v
        ku, a1, a2 = nodes[u]
        kv, b1, b2 = nodes[v]
        if ku == kv == 'nand':
            for t, s in ((a1,a2),(a2,a1)):
                for t2, z in ((b1,b2),(b2,b1)):
                    if t == t2 and nodes[t][0] == 'nand' and sorted(nodes[t][1:]) == sorted((s,z)):
                        kind, left, right = 'xor', s, z
        wires.append(len(nodes))
        nodes.append((kind,left,right))
    target = wires[-1] if gates else 1
    used = {target}
    for i in reversed(range(n+2, len(nodes))):
        if i in used:
            used.update(nodes[i][1:])
    return nodes, sorted(used), target

def prepare(n,gates):
    nodes, used, root = compile_net(n,gates)
    forms, pairs = {}, []
    for i in used:
        op, l, r = nodes[i]
        if op == 'const': forms[i] = l
        elif op == 'input': forms[i] = 2 << l
        else:
            a,b = forms[l],forms[r]
            if op == 'xor': out = a ^ b
            elif a == 0 or b == 0 or a == b ^ 1: out = 1
            elif a == 1 or a == b: out = 1 ^ b
            elif b == 1: out = 1 ^ a
            else:
                out = 2 << (n+len(pairs))
                pairs.append((a,b))
            forms[i] = out
    return pairs,forms[root]

def substitute(form,n,prior):
    out = form & ((2 << n)-1)
    high = form >> (n+1)
    while high:
        low = high & -high
        out ^= prior[low.bit_length()-1]
        high ^= low
    return out

def consistent(equations):
    pivots = {}
    for row in equations:
        while row > 1 and row.bit_length() in pivots:
            row ^= pivots[row.bit_length()]
        if row == 1: return False
        if row: pivots[row.bit_length()]=row
    return True

def verify(n, prepared, cert):
    pairs,last = prepared
    prior, equations = [], []
    for (a,b),bit in zip(pairs,cert,strict=True):
        equations.append(substitute(a,n,prior)^bit)
        prior.append(1 ^ (substitute(b,n,prior) if bit else 0))
    equations.append(substitute(last,n,prior)^1)
    return consistent(equations)

def evaluate(n,gates,x):
    wires=[1,*x]
    for a,b in gates:
        wires.append(1^((wires[a] if a<len(wires) else 1)&(wires[b] if b<len(wires) else 1)))
    return wires[-1] if gates else 1

from collections import Counter

def rank_plan(net):
    pairs,last = net
    options = [[(a,b),(b,a),(1^a^b,a)] for a,b in pairs]
    frequency=Counter(left>>1 for opts in options for left,_ in opts)
    pivots, basis, oriented, masks = {}, [], [], []
    def reduce(row):
        comb=0
        while row and row.bit_length() in pivots:
            value, index=pivots[row.bit_length()]
            row ^= value
            comb ^= 1<<index
        return row,comb
    for opts in options:
        a,b=min(opts,key=lambda pair:(bool(reduce(pair[0]>>1)[0]),-frequency[pair[0]>>1]))
        row,comb=reduce(a>>1)
        if row:
            j=len(basis)
            pivots[row.bit_length()]=row,j
            basis.append(row)
            comb ^= 1<<j
        oriented.append((a,b))
        masks.append((a&1,comb))
    return (oriented,last),basis,masks

def compressed_verify(n,plan,cert):
    net,_,masks=plan
    return verify(n,net,[c^((m&cert).bit_count()%2) for c,m in masks])

def compress(n,net,plan,x):
    bits=sum(b<<i for i,b in enumerate(x))
    for i,(a,b) in enumerate(net[0]):
        v=(bits<<1)|1
        y=1^(((v&a).bit_count()%2)*((v&b).bit_count()%2))
        bits|=y<<(n+i)
    return sum(((bits&row).bit_count()%2)<<j for j,row in enumerate(plan[1]))

def rank_check(n,gates):
    net=prepare(n,gates)
    plan=rank_plan(net)
    sat=False
    for x in product(range(2),repeat=n):
        if evaluate(n,gates,x):
            sat=True
            assert compressed_verify(n,plan,compress(n,net,plan,x))
    assert sat==any(compressed_verify(n,plan,t) for t in range(1<<len(plan[1])))

for gs in product(product(range(5),repeat=2),repeat=2): rank_check(2,gs)
r2=Random(1703)
for _ in range(300):
    n,s=r2.randrange(1,7),r2.randrange(1,9)
    rank_check(n,[(r2.randrange(n+s+1),r2.randrange(n+s+1)) for _ in range(s)])
def rank_control():
    gates=[]
    def nand(a,b):
        gates.append((a,b))
        return 128+len(gates)
    def xor(a,b):
        t=nand(a,b)
        return nand(nand(a,t),nand(b,t))
    # 16 groups, 7 XOR diamonds and 2 NANDs per group, plus 31 final XORs.
    gates.extend([(0,0)]*(4096-16*30-31*4))
    terms=[]
    for i in range(1,129,8):
        q=xor(xor(i,i+1),xor(i+2,i+3))
        for s in (xor(i+4,i+5),xor(i+6,i+7)):
            terms.append(nand(s,xor(s,q)))
    out=terms[0]
    for term in terms[1:]: out=xor(out,term)
    return gates
g=rank_control()
net=prepare(128,g)
plan=rank_plan(net)
assert (len(g),len(net[0]),len(plan[1]))==(4096,32,16)
for t in range(1<<16):
    # On this control the predicate is SAT under every group parity except all ones.
    assert compressed_verify(128,plan,t)==(t != 65535)
print('Shared-difference control: 32 nonlinear gates, rank 16; 65535/65536 certificates feasible.')
~~~

## Exact bounded-rank search for dependent operands

The three legal orientations at a genuine binary nonlinear gate are the three nonzero selectors in a two-dimensional binary plane P_i. To find a selector space of rank at most k on the chosen representation one can use a deterministic search costing O(3^k poly(input size)). This applies even if the operands of different gates are linearly dependent. First reduce forms modulo any *proved* affine equations on the joint trace (retaining their offsets). In quotient coordinates a constant operand or two dependent linear parts make the Boolean product affine; retain that affine gate equation in the verifier. The remaining planes have dimension two. Any original satisfying witness supplies the quotient coordinates. Substitution into the original verifier or retention of all proved affine equations prevents enlargement of the accepted relation.

Start with S=0. If S meets every plane nontrivially, return its basis. If the budget is exhausted, report failure. Otherwise pick any missed plane P and branch on adding each of its three nonzero vectors to S. Each branch increases dimension by exactly one. If a solution space T containing S exists, then T contains at least one of those three vectors, so induction preserves a successful branch. Conversely every returned space supplies one legal orientation per gate and the earlier linearized verifier. At most (3^(k+1)-1)/2 nodes are visited. A branch stores an echelon basis; reducing two generators of P modulo S suffices to test whether their images lose rank. A safe pruning bound: greedily collect missed planes whose two-dimensional images in the quotient form a direct sum. If j such planes are collected, every feasible extension has at least j new independent directions. Merely checking pairwise trivial intersections does not prove the same bound for three or more planes. Recover actual selected rows in the original planes after finding S, and restore the affine offsets during decoding.

Iterative deepening through k finds the minimum rank when within budget. In particular a logarithmic budget gives polynomial *discovery* time for every family with a logarithmic optimum, without assuming a good orientation is supplied or found by a heuristic. After preprocessing, enumerating 2^k linear systems decides those circuits with perfect one-bit WE on the promise family; alternatively the split backend has the counts given above. Failing at budget k rules out only this selector representation up to rank k, and the compiler may fall back to the original backend. The budget must be charged to Enc; it need not be rerun in Dec for the public decision mode. This gives no worst-case logarithmic rank bound.

~~~python
from itertools import combinations

def span(vectors):
    s = {0}
    for v in vectors:
        s |= {x^v for x in s}
    return frozenset(s)

def search(planes, s, budget):
    p = next((p for p in planes if not p & s), None)
    if p is None:
        return s
    if budget:
        for v in sorted(p):
            answer = search(planes, s | {x^v for x in s}, budget-1)
            if answer is not None:
                return answer
    return None

planes = sorted({frozenset((a,b,a^b)) for a,b in combinations(range(1,8),2)},
                key=sorted)
spaces = {span(vs) for n in range(4) for vs in combinations(range(1,8),n)}
checked = 0
for n in range(len(planes)+1):
    for family in combinations(planes,n):
        optimum = min(len(s).bit_length()-1 for s in spaces if all(s&p for p in family))
        for k in range(4):
            ans = search(family,frozenset({0}),k)
            assert (ans is not None)==(optimum<=k)
            if ans is not None:
                assert len(ans)<=2**k and all(ans&p for p in family)
            checked += 1
print(checked,"families/budgets agree with exhaustive subspace enumeration")
~~~

## Adaptive certificates for publicly selected subcircuits

A fixed space meeting every operand plane can be unnecessarily large when a circuit selects which checks matter. Use a publicly specified polynomial-time rule that at each step requests the value of an affine form on the original trace or finishes with an affine feasibility system. Restrict the system by every requested equality. In simplifying the verifier allow substitution, pruning a multiplexer with a fixed address, and deletion of gates that no longer feed the output. When deleting gates, retain enough definitions to justify any already requested internal-wire equality. Equivalently keep those equalities as additional outputs of the original verifier during simplification. Each terminal system must be equisatisfiable with the restricted original verifier; a contradiction is a valid rejecting terminal. Every satisfying trace must reach a terminal in at most d requests. This last requirement is about *every witness supplied to Dec*, even if a different witness reaches an earlier terminal. It follows structurally in the multiplexer case below.

Compile one verifier on d response bits: replay the rule, accept exactly if it finishes within the budget and its terminal affine system is consistent; ignore trailing bits. Dec obtains its certificate by evaluating the original accepting trace and answering each request, padding to d bits. A forged response string can choose any history, but cannot pass a terminal with inconsistent requested values. Any accepting terminal has an original satisfying trace by the terminal equivalence. These two implications prove ordinary WE transport, without requiring a NO trace to finish within d. Defining the verifier on a timeout to reject is essential. A mere heuristic bound seen on sampled accepting traces cannot justify correctness. The replay requires at most d polynomial-time steps plus one affine solve; a uniform Boolean verifier can simulate this bounded computation without unrolling an exponential decision tree. Its circuit size and depth must still be included in backend costs.

For an explicit family let the d0 address bits select one of m=2^d0 public predicate circuits P_i, all on the same primary input vector. A source witness consists of address and data and is accepted by P_address. Each arm has its own static selector certificate of dimension k_i, without a common space across arms. Take the address followed by max_i k_i bits, and evaluate the chosen arm's consistency verifier on just its own prefix. The total certificate length is d0+max_i k_i. Building a circuit with all m branch verifiers and a final multiplexer costs their total size, polynomial in the explicit arm descriptions. Splitting this single certificate for the existing two-half backend uses 2^floor(d/2) key entries and 2^ceil(d/2) attribute entries for d=d0+max_i k_i. No exponential search over all data bits or semantic recognition of arbitrary multiplexers is required. Irregular policies can instead use the general bounded replay if its accepting-depth guarantee is proved.

For P_i(u,v)=u_i v_i, the m product planes on disjoint coordinates form a direct sum. A single space meeting all m therefore needs rank at least m, even before counting any selector logic. After fixing the address only one product remains, so the preceding compiler uses at most log2(m)+1 response bits. The arm can even decide its own satisfiability without the final bit in this simple example; the example only separates simultaneous and branch-specific linearization on this representation. If a concrete witness must satisfy additional conditions shared across arms, include them inside every chosen verifier or prove them separately; ignoring them would change the language. General CircuitSAT has no established sublinear or logarithmic bound on accepting depth. The optimization uses no new assumption and retains the false-statement security of the selected backend.

~~~python
from itertools import product
m = 4
# Extra affine restrictions are shared by all branches and must survive pruning.
for rhs in product(range(2), repeat=m):
    for i in range(m):
        def valid(data):
            u,v = data[:m],data[m:]
            return all((a^b)==r for a,b,r in zip(u,v,rhs)) and u[i]*v[i]==1
        # After guessing z=u_i, enforce u_i=z, z*v_i=1, and all affine rows.
        # Eliminate each u_j=v_j XOR rhs_j. Solve the remaining one-bit system.
        cert = [any((v^rhs[i])==z and z*v==1 for v in range(2)) for z in range(2)]
        found = [False,False]
        for data in product(range(2),repeat=2*m):
            if valid(data):
                found[data[i]]=True
                assert cert[data[i]]
        assert found == cert
print("64 address/restriction cases; all 16384 source traces and both response bits checked")
~~~

## Packing unequal branch certificates into a single ABE setup

The padded address in the preceding construction wastes certificate slots when branch ranks differ. Use the disjoint union instead. For each public arm i, let s_i=2^k_i be its number of response strings (or another certified positive cardinality with efficient ranking and unranking). Compute offsets o_i=sum_(j<i) s_j and S=sum_i s_i. An original witness for branch i with local certificate t uses the integer z=o_i+rank_i(t). For any public L>=1 use K=ceil(S/L) policy keys and L attributes; take L<=S. Key a on attribute b forms z=aL+b, rejects if z>=S, locates the unique half-open interval [o_i,o_i+s_i), and evaluates that arm's *full* consistency verifier on unrank_i(z-o_i). The actual witness picks a=z div L and b=z mod L. There is no requirement that a row or a column alone identify an arm. Every cross pair either rejects or denotes one well-formed trial. On an original NO every pair is unauthorized; on an original YES each original accepting witness supplies its own authorized pair. The ordinary split-ABE proof applies with the actual K and L and its original adversary and multi-key conditions. No additional security assumption is needed for indexing.

Only the explicit list of arms, offsets and verifier descriptions is needed. Offset generation takes polynomial bit time in m and max k_i, even when S is exponential. Compile interval comparisons, subtraction and the local verifier selection as Boolean circuits, with polynomial size in the list and bit lengths. A sequential machine can scan the list; a binary comparison tree on its own is not a logarithmic-size Boolean circuit for arbitrary verifiers. Include policy circuit sizes, setup, entry lengths and indexing work in total cost estimates. For fixed per-entry weights A and B, any L gives weighted entry cost A ceil(S/L)+BL. Testing the clipped integers adjacent to sqrt(AS/B) gives a feasible size, while comparisons for the discrete optimum should use the actual ceiling function. For equal weights a near-square rectangle gives O(sqrt(S)) entries per side. No existential search or census of the accepting certificates is needed. Thus a few long branches pay in proportion to their own capacity rather than replicating that capacity for every arm.

For example, with 255 arms of rank 8 and one of rank 32, S=2^32+65280. The previous padded 40-bit certificate required 2^20 keys and 2^20 attributes in a balanced split. Choosing L=65536 now gives K=65537 and L=65536. This is a count of cryptographic entries, not a measured byte or time reduction. More generally, if every arm is small enough for affordable public enumeration, direct decision remains preferable. Within a public time budget one may also test selected cheap arms before packing: on finding any valid certificate emit the payload directly with a public mode bit so *every* original witness can decode it; drop an arm only after exhaustive rejection or another sound rejection certificate. Keep incompletely checked arms in the packed domain. This test uses only the statement, hence on NO its mode and chosen layout are independent of the payload. Empty residual domain after exhaustive rejection permits a fixed dummy ciphertext. Neither packing nor partial enumeration bounds S for general circuits.

~~~python
from itertools import product
for ranks in product(range(4), repeat=3):
    sizes = [1<<k for k in ranks]
    S = sum(sizes)
    for L in range(1,S+1):
        K = (S+L-1)//L
        seen = set()
        for a,b in product(range(K),range(L)):
            z = a*L+b
            if z>=S:
                continue
            i = next(i for i in range(len(sizes)) if z<sum(sizes[:i+1]))
            t = z-sum(sizes[:i])
            assert divmod(sum(sizes[:i])+t,L)==(a,b)
            seen.add((i,t))
        assert seen=={(i,t) for i,s in enumerate(sizes) for t in range(s)}
S = (1<<32)+255*256
assert (S+65535)//65536==65537
print("64 rank profiles; all rectangular widths and cross pairs checked")
~~~
