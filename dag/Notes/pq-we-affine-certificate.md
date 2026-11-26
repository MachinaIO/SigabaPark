---
title: Compressing CircuitSAT witnesses before split-witness lattice ABE by linearizing nonlinear gates
refs: [definition:WE_CircuitSAT, theorem:AdvancedEncryption.WE.XWE.linearized_certificate]
tags: [witness-encryption, circuit-sat, lattice, preprocessing]
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
