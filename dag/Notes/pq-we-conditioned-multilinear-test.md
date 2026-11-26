---
title: One-bit WE from conditional multilinearity, with one public-field evaluation per restriction
refs: [definition:WE_CircuitSAT, theorem:AdvancedEncryption.WE.PIT.boolean_cube_single_seed, note:we-circuitsat-bruteforce-explicit-cost]
tags: [witness-encryption, circuit-sat, identity-testing, baseline]
---

## Construction for the registered relation

Normalize the public NAND circuit into constants, inputs, XOR, complement and binary NAND. Forward references read true at that gate, as in evalGates. Record a conservative input dependency set at each wire by taking unions. At each remaining product gate, add the intersection of its two operand dependency sets to B. Treat NAND(a,a) as a complement. Four-NAND XOR diamonds can be contracted before the scan; both rewrites are Boolean identities. Let t=|B|. These computations use the circuit description and have polynomial cost.

Assigning the t bits in B makes every remaining product multiply polynomials on disjoint sets of unassigned variables. Over characteristic two use 1+ab for NAND, 1+a for complement and addition for XOR. For every restriction u the resulting polynomial f_u on m=128-t variables is multilinear, by induction on the gates. Its cube values are exactly the bits of the original restricted verifier. An arbitrary circuit still has such a B, possibly the entire input. The intersection test is sufficient; the construction does not require finding a minimum B.

Use a fixed polynomial basis of GF(2^256). Enc samples a uniform element A and evaluates the circuit with the m remaining inputs set to A, A², A⁴, ..., A^(2^(m-1)), in the same order for every restriction u. Return the single bit beta AND the disjunction of “evaluation is nonzero” over the 2^t restrictions. Dec returns that bit. Sample the field element with 256 unbiased bits and precompute its successive squares once. Neither an exponential list of coefficients nor a subset table is generated. The work is polynomial preprocessing plus 2^t circuit evaluations over the field and the fixed costs of reading the registered encoding. There is no cryptographic setup.

On a NO instance every restricted polynomial vanishes on the Boolean cube. Multilinearity forces every coefficient to be zero, so both ciphertext laws are exactly the same point mass for every seed. On a YES instance fix one satisfying witness independently of the randomness. Its restriction has a nonzero polynomial. A monomial on variables indexed by S maps to degree sum(2^i for i in S); these exponents are distinct. Hence at most 2^m-1 field elements are roots. Missing every restriction implies missing that one, so per-witness error is at most (2^m-1)/2^256 < 2^-128. This matches the registered correctness quantifier. The Lean theorem proves both claims for the coefficient representation and cube evaluations, over any finite field. Specializing the evaluator uses the characteristic-two gate semantics above.

Multilinearity must be enforced. An expression x(1+x) vanishes at both bits but generally gives a nonzero field value. The overlap test fixes x before this multiplication. This method uses exact rejection on NO instances, unlike an argument whose false statements might still have accepting proofs. It takes inspiration from public polynomial evaluations in [Praxis, Section 4.4](https://eprint.iacr.org/2026/2971); this test uses neither a hidden point nor bilinear group operations.

## Optional lattice tradeoff and comparison

One can instead make u the witness of a shorter relation with public seed A and circuit predicate “the field evaluation is nonzero.” Conversion from a supplied witness simply selects B. Apply the two-table ABE construction of [ePrint 2017/874, Section 3.2](https://eprint.iacr.org/2017/874.pdf) to the t bits. Every NO circuit rejects every pair on every seed, and one valid original witness selects an authorized pair except on the root event. The balanced split uses 2^floor(t/2) keys and 2^ceil(t/2) encrypted attributes. Reserve the rest of the correctness budget for the ABE error; its concrete LWE reduction, depth and tape costs remain separate obligations. When t=0 the one-bit construction above takes one evaluation and needs no ABE at all. With large t one should compare against the original ABE verifier and the exhaustive machine: even at equal enumeration count, extension-field arithmetic has a price.

## Full-size controls

A 4096-NAND positive control computes the product of 64 pairwise XORs on disjoint input pairs. All 128 inputs are essential and its expanded multilinear polynomial has 2^64 distinct nonzero monomials. The negative control XORs this product with an independently computed product of the same factors in reverse order. Both have t=0 after the specified rewrites. The positive control needs 63 field multiplications in the product chain, plus the sequence of squares, additions and circuit handling. The positive control returned nonzero at seeds 2, 3, 5, 7, 11 and 42 and zero at 0 and 1. The negative control returned zero at all eight; the mathematical bound applies to the full seed space. These controls demonstrate avoidance of enumeration, not average-case behavior on general circuits.

The reference implementation checks the zero-seed-count bound for each individual certificate on all 625 two-input two-gate circuits and 300 seeded small cases over GF(16). The full-size examples use X^256+X^10+X^5+X^2+1, verified locally by the binary irreducibility criterion (gcd at 128 Frobenius squarings and equality at 256). The implementation below is a semantic prototype. An end-to-end machine realization and its worst-case clock and description size are open.

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

def plan(n,gates):
    nodes,used,root=compile_net(n,gates)
    inputs={}
    overlap=0
    for i in used:
        op,a,b=nodes[i]
        if op=='input':inputs[i]=1<<a
        elif op=='const':inputs[i]=0
        else:
            x,y=inputs[a],inputs[b]
            inputs[i]=x|y
            if op=='nand' and a!=b:overlap|=x&y
    return (nodes,used,root,overlap,n)

def mul(a,b,f):
    s=f.bit_length()-1
    res=0
    while b:
        if b&1:res^=a
        b>>=1
        a=(a<<1)^(f if a>>(s-1) else 0)
    return res

def powers(m,seed,f):
    xs=[]
    for _ in range(m):
        xs.append(seed)
        seed=mul(seed,seed,f)
    return xs

def run(pre,bits,pts,f):
    nodes,used,root,ov,n=pre
    vals={}
    aidx=bidx=0
    inp=[]
    for i in range(n):
        if ov>>i&1:inp.append(bits>>bidx&1);bidx+=1
        else:inp.append(pts[aidx]);aidx+=1
    for i in used:
        op,a,b=nodes[i]
        if op=='input':vals[i]=inp[a]
        elif op=='const':vals[i]=a
        elif op=='xor':vals[i]=vals[a]^vals[b]
        elif a==b:vals[i]=1^vals[a]
        else:vals[i]=1^mul(vals[a],vals[b],f)
    return vals[root]

def brute(n,gates,x):
    w=[1,*x]
    for a,b in gates:
        w.append(1^((w[a] if a<len(w) else 1)&(w[b] if b<len(w) else 1)))
    return w[-1] if gates else 1

def test(n,gates):
    f=0b10011
    pre=plan(n,gates)
    ov=pre[3]
    t=ov.bit_count()
    true_at=set()
    for x in product(range(2),repeat=n):
        if brute(n,gates,x):
            true_at.add(sum(x[i]<<j for j,i in enumerate(i for i in range(n) if ov>>i&1)))
    for cert in range(1<<t):
        zeros=sum(run(pre,cert,powers(n-t,seed,f),f)==0 for seed in range(16))
        if cert in true_at:assert zeros<=2**(n-t)-1
        else:assert zeros==16

for g in product(product(range(5),repeat=2),repeat=2):test(2,g)
rng=Random(2972)
for _ in range(300):
    n,s=rng.randrange(1,5),rng.randrange(1,12)
    test(n,[(rng.randrange(n+s+1),rng.randrange(n+s+1)) for _ in range(s)])
def control(negative):
    # Build two equal polynomials in different multiplication orders for the NO control.
    used=64*4+63*2+(63*2+4 if negative else 0)
    g=[(0,0)]*(4096-used)
    def nand(a,b):
        g.append((a,b));return 128+len(g)
    def xor(a,b):
        t=nand(a,b);return nand(nand(a,t),nand(b,t))
    def fold(terms):
        out=terms[0]
        for v in terms[1:]:
            z=nand(out,v);out=nand(z,z)
        return out
    a=[xor(i,i+1) for i in range(1,129,2)]
    v=fold(a)
    if negative:xor(v,fold(a[::-1]))
    return g
f=(1<<256)|(1<<10)|(1<<5)|(1<<2)|1
for flag in [False,True]:
    g=control(flag); pre=plan(128,g)
    assert pre[3]==0 and len(g)==4096
    instances=[run(pre,0,powers(128,seed,f),f)!=0 for seed in [0,1,2,3,5,7,11,42]]
    assert instances==([False]*8 if flag else [False,False,True,True,True,True,True,True])
    print(flag,'selected bits',pre[3].bit_count(),'results',instances)
~~~
