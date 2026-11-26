---
title: Exact one-bit encryption by signed-path analysis on the registered NAND evaluator
refs: [definition:WE_CircuitSAT, definition:WE_WirePolarity, theorem:AdvancedEncryption.WE.CircuitSAT.polarity_encBit_exact, note:we-circuitsat-bruteforce-explicit-cost]
tags: [witness-encryption, circuit-sat, baseline]
---

The conditional multilinearity test of PR #73 removes no additional live input on its 100 dense layered controls. All paths from an input to the final gate in each such circuit have the same depth. Repeated use therefore preserves polarity, even when the two children of a gate depend on exactly the same inputs. This leads to a complementary deterministic preprocessing step.

Associate two sets P,N to each wire. Input i starts at ({i},empty) and a constant at (empty,empty). NAND replaces the pair by the union of the children's negative sets and the union of their positive sets in that order. Compute only in gate order; wire zero and unavailable forward reads are constant true. At the output let b be the cardinality of the intersection. Enumerate the b mixed bits, set positive-only inputs true and all other unchosen inputs false. Encrypt beta as one bit, beta AND the disjunction of the results. Decryption returns that bit. An optional early exit at the first accepting evaluation preserves the result.

The Lean theorem relates this running code to CircuitSAT.Satisfies for every n and gate count, including empty circuits and forward reads. It proves the stronger witness conversion: restricting any valid witness to its mixed bits and lifting it at the extrema gives another valid witness. Each wire can only increase when all its positive coordinates increase and all negative coordinates decrease. For a NAND, its two operands can only decrease in the required comparison. This is sufficient even when the two sets overlap. Consequently the new evaluator gives perfect correctness and identical one-bit ciphertexts for false circuits. This also allows the balanced split-witness ABE route to replace n with b and use the original verifier with fixed public inputs. The finite enumeration is implemented in Lean; a clocked tape-machine submission and its explicit cost are still open.

Two signed bit masks per wire take O((n+s) ceiling(n/W)) machine words for n inputs, s gates and word width W in the packed implementation. The forward pass takes O(s ceiling(n/W)) word operations apart from initialization. A full scan then uses at most 2^b evaluations. The proof's Lean list lookup and Finset operations have their own costs; this word-operation bound is not its tape clock. If the sets coincide on all live inputs there is no saving over dead-input removal.

## Sensitivity to changes in wiring

Rows below use 100 circuits each, 128 inputs, 4096 gates. In the layer family there are 32 successive layers of width 128 and two distinct parents per gate drawn from the preceding layer. For each seed start with the identical baseline and reroute one operand on the specified number of distinct gates to the layer two steps back. The arbitrary-parent family draws both operands uniformly without replacement from the earlier wires, including the constant. Endpoint hits count circuits accepting at least one of the two assignments that set all mixed bits uniformly to zero or one and fix the remaining bits at the extrema.

| Family | Mixed bits min / median / max | Median live inputs | Endpoint hits |
|---|---:|---:|---:|
| Layered | 0 / 0 / 0 | 102.5 | 100 |
| 1 reroute | 0 / 8 / 109 | 102.5 | 100 |
| 8 reroutes | 46 / 103 / 110 | 103 | 100 |
| 32 reroutes | 93 / 103 / 111 | 103 | 100 |
| 128 reroutes | 94 / 103.5 / 112 | 103.5 | 100 |
| 512 reroutes | 94 / 105 / 115 | 105 | 98 |
| Arbitrary earlier parents | 0 / 7.5 / 36 | 43 | 100 |

The unperturbed layered family is especially easy: with no constants in the gates, all ones already satisfies every even-depth circuit in that family. The endpoint counts also expose easy positives away from this case. They do not estimate the cost on hard SAT or UNSAT instances.

A paired full-size control exercises actual rejection. Conjoin 125 positive input literals with inequalities between input pairs (1,2) and (2,3). In the NO variant also require (1,3) to differ. Each inequality uses a four-NAND XOR, and unused constant gates pad both variants to 4096. Both have 128 syntactically live inputs, exactly three mixed bits and eight residual assignments. The YES variant accepts exactly 010 and 101. The NO variant rejects all eight. Small differential checks verify each accepting witness conversion and both directions of the satisfiability test on all 625 two-input two-gate circuits and 300 seeded circuits.

~~~python
from itertools import product
from random import Random
from statistics import median

def signs(n,gates):
    data=[(0,0)]+[(1<<i,0) for i in range(n)]
    for a,b in gates:
        ap,an=data[a] if a<len(data) else (0,0)
        bp,bn=data[b] if b<len(data) else (0,0)
        data.append((an|bn,ap|bp))
    return data[-1] if gates else (0,0)

def value(n,gates,x):
    data=[1]+[(x>>i)&1 for i in range(n)]
    for a,b in gates:
        data.append(1^((data[a] if a<len(data) else 1)&(data[b] if b<len(data) else 1)))
    return data[-1] if gates else 1

def check(n,gates):
    p,q=signs(n,gates)
    mixed=p&q
    vals=[]
    for x in range(1<<n):
        orig=value(n,gates,x)
        restricted=value(n,gates,(x&mixed)|(p&~q))
        assert not orig or restricted
        vals.append(orig)
    assert max(vals)==max(value(n,gates,x|(p&~q)) for x in range(1<<n) if x&~mixed==0)

for gates in product(product(range(5),repeat=2),repeat=2):check(2,gates)
for seed in range(300):
    r=Random(seed)
    n,s=r.randint(1,7),r.randint(0,12)
    check(n,[tuple(r.randrange(1+n+s) for _ in range(2)) for _ in range(s)])

def build_topo(r):
    return [tuple(r.sample(range(129+j),2)) for j in range(4096)]

def build_layers(r,delta):
    gs=[]
    for layer in range(32):
        start=1+128*layer
        for _ in range(128):
            gs.append(tuple(r.sample(range(start,start+128),2)))
    # Perturb a fixed baseline so comparisons are paired by seed.
    for j in r.sample(range(128,4096),delta):
        a,b=gs[j]
        gs[j]=(a,r.randrange(1+128*(j//128-1),1+128*(j//128)))
    return gs

for label,delta in [('layer',0),('skip1',1),('skip8',8),('skip32',32),('skip128',128),('skip512',512),('topo',None)]:
    counts=[]; hit=0; active=[]
    for seed in range(100):
        r=Random(seed)
        g=build_topo(r) if delta is None else build_layers(r,delta)
        p,q=signs(128,g)
        counts.append((p&q).bit_count())
        active.append((p|q).bit_count())
        hit+=bool(value(128,g,p&~q) or value(128,g,p))
    print(label,min(counts),median(counts),max(counts),median(active),hit)

def parity_control(negative):
    # Hash-free NAND net with 125 unate wires and three mixed inputs.
    pairs=[(1,2),(2,3)]+([(1,3)] if negative else [])
    live=4*len(pairs)+2*(125+len(pairs)-1)
    g=[(0,0)]*(4096-live)
    def nand(a,b):
        g.append((a,b));return 128+len(g)
    def and_(a,b):
        c=nand(a,b);return nand(c,c)
    def xor(a,b):
        c=nand(a,b);return nand(nand(a,c),nand(b,c))
    ts=[xor(a,b) for a,b in pairs]+list(range(4,129))
    out=ts[0]
    for a in ts[1:]:out=and_(out,a)
    return g
for negative in (False,True):
    g=parity_control(negative)
    p,q=signs(128,g)
    assert len(g)==4096 and p&q==7 and (p|q).bit_count()==128
    bits=[value(128,g,z|(p&~q)) for z in range(8)]
    assert sum(bits)==(0 if negative else 2)
    print('paired control',negative,bits)
~~~
