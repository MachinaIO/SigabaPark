---
title: Projected wiring joins, local NAND degree and exact boundary keys
refs: [definition:WE_CircuitSAT_Capped, definition:ProjectedWiringJoin, theorem:ProjectedWiringJoin.supportOverlap]
tags: [witness-encryption, circuit-sat, streaming]
---

## Directed projection on a redundant trace

Use 129 source positions (constant and 128 inputs), followed by 4096 triples of independently supplied parent reads and output. The common address has n=12417 bits. One reader B accepts exactly the product of legal NAND rows subject to terminal acceptance. The other reader A checks wiring consistency, the true constant and any other required source pins. Map forward/self/unavailable parents to the true source. The same total relation results if the constant test is moved into B. Every genuine witness gives a single consistent accepting trace; each trace satisfying both has one actual 128-bit input.

Suppose on B-support the indicator A is a binary polynomial of degree ≤t. Take all d=Σ_{j≤t} binomial(n,j) squarefree monomials, including one. Read bits in the B program order with unread bits initially zero. Setting bit i to e copies e times feature S minus {i} into each feature S containing i, leaving every other feature alone. These maps are linear for fixed e. Per state store a basis for the span of attained feature vectors, take the image along each transition and take sums at merges. By induction the accepting basis spans exactly all attained rows, although individual vectors in the span need not themselves occur. Convert each monomial bit v_j to a pair (1+v_j,v_j), using the constant feature for the 1. Write L for an exact row basis of these binary selectors. Write h for the public A coefficients placed in the second positions; other positions are zero.

For the directed VOLE interpretation expose sender (u⁰,v⁰), receiver multiplier Δ, and all noise shares, all sampled independently of the payload. In a one-layer binary linear evaluation each address selects one position from every pair. The base receiver values are w⁰=v⁰+Δu⁰, now known. Issue only Y=L(w⁰+βh) from the receiver base. For B-accepted x solve for row coordinates of its selector in L, apply to Y, and reconstruct the remaining public noise. The offset from the ordinary public baseline equals βA(x), hence equals β at a witness. If NO, all attained rows annihilate h, so Lh=0 and the *whole* joint transcript is equal on the very same coins. Conversely on YES, Lh≠0 and anybody can obtain β from Y−Lw⁰. h is public. The raw edited vector, which would expose βh even on some NOs, is never emitted. Neither sparse LPN nor a random-oracle theorem is used. The row-selector version is a deterministic functional use of the recursion in [Braun et al., Figure 2](https://opencryptology.org/2025/1644.pdf).

With r basis rows, the projected field payload is r log₂|F| bits and its simplified binary WE residual has r bits. A stored selector basis costs 2dr bits; reconstruction from B instead charges the decoder. O(n w d³) binary operations and O(w d²) bits suffice for dense elimination with bounded width w, excluding framing and the ordinary VOLE data. For n=128,t=2, d=8257 and 2d²=136356098. For the raw n=12417,t=2, d=77097154 and 2d²=11887942309799432 bits; the crude operation bound there can already dominate the cap. The coefficients, basis, mask and projected output are different objects. No universal t=2 representation follows.

## Degree lower bound on actual legal rows

Take 2048 leaves NAND(x,x), then 11 balanced NAND levels with 2047 internal gates, then a final NAND negation. All 4096 gates lie syntactically upstream of the output. Fix the source x=0 and the other primaries, the true constant, and every tree/terminal triple to their legal values on that input. Keep each leaf triple (y_i,y_i,1+y_i) free and independent. Every one of these 2^2048 assignments passes B, including the terminal-one test. A holds precisely at y=0: both redundant leaf reads must match the fixed primary. Every raw bit on this slice is constant or affine in one y_i. Restricting any degree-t raw polynomial and reducing y_i²=y_i cannot increase its degree. The unique multilinear Boolean polynomial for this point indicator is ∏(1+y_i), containing the full 2048-variable monomial. Equivalently its parity over the slice is one, while every monomial missing any y_i has even parity. Degree at least 2048 is necessary, even after quotienting by all identities satisfied by legal NAND triples. The dense basis includes at least binomial(12417,2048)>2^8014 cells. The lower bound is for exact raw-indicator polynomials on B-support. This circuit computes a simple Boolean function; algebraic simplification or a different verifier can avoid its raw degree.

Packing the wiring-error vector s into an extension-field element preserves zero versus nonzero but reverses the desired polarity: s itself is zero at every honest trace. The zero indicator is 1+s^(q−1) for q a power of two. Its compilation must still pay the Boolean degree bound on the displayed slice. A linear span always contains zero, so zero in the span of attained syndromes is no decision test. For example the exact set {01,10} omits zero although its span contains zero. In contrast, vanishing of a fixed linear form on a basis is equivalent to vanishing of that form on every attained row.

## Exact boundary representation

Partition the gates and consistency tests into a left and right side. Expose as separator variables *every* wire/source value constrained by both sides, including a shared primary. Each side enforces its own NANDs and internal wiring equalities. Let S,T be the independently attained assignments of the k separator bits, including the terminal test on its side. If the two partial assignments agree on all shared variables, their union is a single globally consistent accepting witness; restriction gives the converse. This is a criterion on the actual factorization, not a promise that locally chosen representatives happen to agree.

Draw independent fair bits r_z for the 2^k labels z. In fixed slots emit S(z)·r_z on the left and T(z)·(r_z xor β) on the right. The two eligibility computations never intersect their tables. On YES the witness knows the shared label and XORs its two slots. On NO the full pair for β=0 at coins r equals the pair for β=1 at coins r xor T. This transformation permutes all coins. It proves equality of the complete fixed-length keys even with coherent audience processing. The theorem supportOverlap gives the converse: a single common label prevents any overlap of the two key supports. If local eligibility flags are public or transmitted, they depend solely on the circuit and preserve these statements.

The emitted pair has 2^(k+1) bits and consumes 2^k random bits. Each side can enumerate separator assignments and evaluate its internal existential projection by exact Boolean variable elimination. For a supplied elimination order of induced width p (largest remaining neighbor count), a direct upper bound is O(2^k m 2^(p+1)) Boolean table operations for m bounded-arity input factors and all separator assignments, using O(m 2^(p+1)) workspace per assignment and output table storage. Factor collection and indexing add polynomial overhead. No result on a circuit is certified unless its actual separator, elimination plan, input parsing, and costs fit. In a general expander wiring k or p can be large. On small-width families the same decomposition also gives an efficient SAT algorithm by checking the two final sets; that last intersection is unnecessary for issuing the masked slots.

For the degree-2048 fixture cut immediately above the left 1024-leaf subtree. The entire boundary is (x,left subtree root), four labels. Left evaluates its deterministic subtree at two x values. Right separately evaluates the remaining circuit with an externally supplied left output for each of the four labels. Each local pass costs at most 4096 NAND evaluations with direct topological memoization; a conservative bound for the six independent passes is 24576 evaluations, plus wire bookkeeping. The masked arrays take eight bits and four random bits. For a nonvacuous NO sibling, change leaves 1025 through 2047 (zero-based) to read the output of leaf 1024 on both pins. Leaf 1024 is the first right leaf, with registered wire number 1153. Every edge is backward and all gates still feed the terminal. On YES the two sets are {1,2} and {1}; on NO they are {1,2} and {3}. Labels encode 2x+left_output. Thus both local sides remain feasible on the NO, and the joint NO guarantee is needed. The reference code deliberately makes the local witness evaluations separately.

## Random compression and whole-view risk

Apply a public random binary linear H with s output bits to the two attained separator sets. Emit both masks using independently random bits per compressed label. A true shared witness always decodes. On any NO let D={a+b : a∈S,b∈T}. Zero is absent. Conditioned on H the statistical distance between the two entire issued transcripts is exactly one if D intersects ker H and zero otherwise. The first case follows from decoding at a common label; the second uses the coin permutation. Including the independent public H in the transcript gives exact total variation Pr[D∩ker H≠∅]. This is information-theoretic and need not provide a fast membership search. For independent uniform matrix entries it is at most min(1, |D| 2^(−s)). Only distinct nonzero differences count. For a single fixed witness one does not need a union bound for completeness; NO privacy of the public array does require simultaneous control over all differences. A per-trace bound on a low-degree randomized wiring indicator fails for the same reason: Y−Lw⁰=βLh is exposed, and a single spurious nonzero evaluation can distinguish both conditional supports.

The worst case can be exact. For k≥2 take S of weights 0 or 1 and T of weights ≥2 on k bits. For any nonzero difference of weight ≥2 use its difference with zero; for a unit e_i use e_j and e_i+e_j with j≠i. Then D contains every nonzero vector and every noninjective linear H creates a false join. Both local predicates admit tiny saturating weight counters. A public nonlinear feature telling whether weight is at least two separates this particular pair using one bit, but agreeing on a nonlinear feature must imply a common attainable witness on every instance to use it generically.

## Reproducible finite checks

The program uses registered wire zero for the true constant, 1 through 128 for inputs, and 129 for the first gate. Its helper recurses over the two bounded-depth fixtures; general cost above uses memoization. Expected first two lines give satisfiability flag parameter, both local tables and the size of each message support. It also verifies all nonzero differences on 2 through 8 separator bits and computes the representation sizes.

```python
from itertools import product
from math import comb,log2

def build(no):
    g=[(1153,1153) if no and j>1024 else (1,1) for j in range(2048)]
    layer=list(range(129,129+2048))
    while len(layer)>1:
        out=[]
        for i,j in zip(layer[::2],layer[1::2]):
            g.append((i,j))
            out.append(128+len(g))
        layer=out
    g.append((layer[0],layer[0]))
    return g

def local(g,i,x,cut=None):
    if cut is not None and i==cut[0]: return cut[1]
    if i<=128: return 1 if i==0 else x
    a,b=g[i-129]
    u=local(g,a,x,cut)
    v=u if a==b else local(g,b,x,cut)
    return 1-u*v

def mask(s,t,c,b):
    return tuple(((c>>z)&1) if z in s else 0 for z in range(4)),tuple(
        (((c>>z)&1)^b) if z in t else 0 for z in range(4))
for no in (False,True):
    g=build(no)
    assert len(g)==4096
    root=g[-1][0]
    left=g[root-129][0]
    s={(x<<1)|local(g,left,x) for x in (0,1)}
    t={(x<<1)|y for x,y in product(range(2),repeat=2)
       if local(g,4224,x,(left,y))}
    assert bool(s&t)==(not no)
    assert bool(s&t)==any(local(g,4224,x) for x in (0,1))
    a,b=({mask(s,t,c,h) for c in range(16)} for h in (0,1))
    assert bool(a&b)==no
    print(no,sorted(s),sorted(t),len(a),len(b))
for n in range(2,9):
    S={0}|{1<<i for i in range(n)}
    T=set(range(1<<n))-S
    assert {a^b for a in S for b in T}==set(range(1,1<<n))
for n in (128,12417):
    d=1+n+comb(n,2)
    print(n,d,2*d*d)
print(round(log2(comb(12417,2048)),3))
```

Output begins `False [1, 2] [1] 4 4` and `True [1, 2] [3] 8 8`. The Lean results certify the public-array coupling, recovery and support criterion. The gate-count fixture, degree restriction, cost estimates and hash probability are mathematical or executable evidence. An efficient all-wiring separator, alternative low-degree indicator, and a registered machine clock remain open.
