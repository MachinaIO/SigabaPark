---
title: Exact two-half communication-rank evaluation for the capped Circuit-SAT WE problem
refs: [definition:WE_CircuitSAT_Capped, note:pq-we-local-signature-quotient, theorem:AdvancedEncryption.WE.SplitRank.nand_pair_factors, theorem:AdvancedEncryption.WE.SplitRank.reencode_rows, theorem:AdvancedEncryption.WE.SplitRank.output_span_test]
tags: [witness-encryption, circuit-sat, linear-algebra, baseline]
---

Split the witness into two equal halves. At each gate represent its Boolean truth table over GF(2) as U Vᵀ, with one row of U per left assignment and one row of V per right assignment. Each input bit and the constant true have width one. Unavailable wires read true as in the registered evaluator. NAND on widths r and s admits width 1+rs: concatenate 1 and the tensor products of the two left rows, and do the same on the right. The dot product is 1+fg.

After each gate, choose a basis B of the left rows, so U=A B. Replace right rows by V'=V Bᵀ. Write V'=E C using a row basis C and coefficient matrix E. The new factors are A Cᵀ and E. A has independent columns because its rows include the basis coefficients of the selected rows. Consequently the new width equals rank(V')=rank(U Vᵀ), including width zero. This computes exact ranks using half tables only. At the final gate, a satisfying pair exists exactly when the two factor spans are not orthogonal, or equivalently when the compressed width is positive. Encrypt b as b AND SAT(C) and decrypt by returning the bit. On a false statement both messages give the same ciphertext distribution, even to an unbounded quantum observer. The construction uses an exact public decision procedure; its unresolved requirement for the registered instance is worst-case cost.

For h bits per half, N=2^h rows, G gates and maximum compressed intermediate rank R (including inputs), Gaussian elimination on rows of width D=1+R² takes O(G N D²) indexed bit operations, in addition to input tables and parsing. Tensor formation and the two coordinate changes fit within the same order. The argument allows indexed bit access and ignores address and head motion. It supplies neither a compiled sequential-tape clock nor a description-length bound. The Python verifier below uses packed integers; the operation count is an analytical estimate, not a benchmark at h=64. A restricted rank cutoff would require a fallback.

Distinct row counts can greatly exceed the rank. The inner product of h bits over GF(2) has rank h and 2^h distinct rows. Compute each x_i y_i by two NANDs and sum by successive four-NAND XORs. For partial parity a and next term b the XOR gates compute 1+ab, 1+a+ab, 1+b+ab and a+b. Since b has rank one, multiplying by b cannot increase the rank of a. The intermediate ranks are at most 2h for h≥1. Here exact recompression across the cut differs from enumerating exported wire patterns or independent nonlinear operands.

There is also a witness-preserving worst-case control. For the fixed split append D=AND_i NAND(x_i,y_i) and output (C XOR D) XOR D. Its Boolean output equals C on every assignment. The intermediate D has invertible matrix [[1,1],[1,0]] tensor-powered h times over GF(2), hence rank 2^h. At h=64 this adds 64 + 2×63 + 8 = 198 NANDs. Any circuit with up to 3898 gates can be embedded into the registered 4096-gate format using extra unused padding gates before D and remapping indices to preserve forward-reference semantics (replace each originally unavailable read by constant true). This lower bound concerns this particular gatewise method and fixed split. A semantic simplifier can cancel the wrapper. A cryptographic fallback justified solely by large intermediate rank still has to handle these embeddings.

**Verification scope.** The three accompanying Lean proofs cover the NAND identity, preservation under a supplied row-expansion certificate, and the spanning-family output test. The algorithm for finding bases, circuit induction, cost accounting, examples, and overflow embedding are argued in this note. General under-cap WE and a full quantum security reduction for a cryptographic fallback remain open.

**Reproduction (Python 3.10+).** The checks exhaust all pairs of 2-by-2 Boolean matrices and all two-input two-gate circuits with the registered wire conventions. They also compare every entry and the compressed rank after every gate of 32 seeded six-input circuits and exercise the inner-product and overflow controls on small halves. The structural-control code uses equality in its wrapper; equality also has full rank. The disjointness wrapper above saves NAND gates.

~~~python
"""Exact two-party truth-table factorization over GF(2), integers as packed rows."""
import itertools
import random

def coordinates(rows):
    pivots = {}
    basis = []
    coords = []
    for row in rows:
        x, c = row, 0
        while x:
            pivot = x.bit_length() - 1
            if pivot not in pivots:
                bit = 1 << len(basis)
                basis.append(row)
                pivots[pivot] = (x, c ^ bit)
                c = bit
                break
            y, z = pivots[pivot]
            x ^= y
            c ^= z
        coords.append(c)
    return basis, coords

def dots(basis, row):
    return sum(((v & row).bit_count() % 2) << i for i, v in enumerate(basis))

def compress(left, right):
    base, lcoords = coordinates(left)
    rb, rc = coordinates([dots(base, v) for v in right])
    return [dots(rb, u) for u in lcoords], rc

def tensor(x, y, width):
    value = 0
    while x:
        bit = x & -x
        value |= y << ((bit.bit_length() - 1) * width)
        x ^= bit
    return value

def nand(x, y):
    k = max((v.bit_length() for v in y[1]), default=0)
    return compress(*[[1 ^ (tensor(a,b,k) << 1) for a,b in zip(xs,ys)]
                      for xs,ys in zip(x,y)])

def verify(f, table):
    u,v=f
    assert [[(a & b).bit_count()%2 for b in v] for a in u] == table
    rows=[sum(bit<<j for j,bit in enumerate(r)) for r in table]
    rank=len(coordinates(rows)[0])
    assert max(v).bit_length()==rank
    assert bool(any(rows))==bool(rank)

def check():
    rng=random.Random(128)
    m=0
    for a,b in itertools.product(range(16),repeat=2):
        def mat(n):
            return [[(n>>(2*i+j))&1 for j in range(2)] for i in range(2)]
        def fac(n):
            return compress([n&3,n>>2],[1,2])
        verify(nand(fac(a),fac(b)),[[1^(x&y) for x,y in zip(r,s)] for r,s in zip(mat(a),mat(b))])
        m+=1
    for _ in range(32):
        d=8
        wires=[]
        truth=[]
        for i in range(6):
            u=[(j>>i)&1 for j in range(d)] if i<3 else [1]*d
            v=[1]*d if i<3 else [(j>>(i-3))&1 for j in range(d)]
            wires.append(compress(u,v))
            truth.append([[x&y for y in v] for x in u])
        for _ in range(64):
            a,b=rng.choices(range(len(wires)),k=2)
            w=nand(wires[a],wires[b])
            t=[[1^(x&y) for x,y in zip(r,s)] for r,s in zip(truth[a],truth[b])]
            verify(w,t)
            wires.append(w)
            truth.append(t)
    print(f'{m} exhaustive 2x2 NAND pairs; 32 six-input circuits x 64 gates; exact entries, rank and satisfiability passed')
if __name__=='__main__':
    check()

def structural_controls(n):
    count = 1 << n
    ids = list(range(count))
    wires = [compress([(a >> i) & 1 for a in ids], [1]*count) for i in range(n)]
    wires += [compress([1]*count, [(b >> i) & 1 for b in ids]) for i in range(n)]
    def gate(x,y):
        v=nand(x,y)
        wires.append(v)
        return v
    def xor(x,y):
        t=gate(x,y)
        return gate(gate(x,t),gate(y,t))
    def both(x,y):
        t=gate(x,y)
        return gate(t,t)
    def neg(x):
        return gate(x,x)
    pairs=list(zip(wires[:n],wires[n:2*n]))
    terms=[both(x,y) for x,y in pairs]
    inner=terms[0]
    for term in terms[1:]:
        inner=xor(inner,term)
    verify(inner,[[(i&j).bit_count()%2 for j in ids] for i in ids])
    ranks_inner=[max(v).bit_length() for _,v in wires]
    eqs=[neg(xor(x,y)) for x,y in pairs]
    e=eqs[0]
    for eq in eqs[1:]:
        e=both(e,eq)
    verify(e,[[int(i==j) for j in ids] for i in ids])
    output=xor(xor(inner,e),e)
    verify(output,[[(i&j).bit_count()%2 for j in ids] for i in ids])
    print(f'{n}+{n} bits: inner-product rank {max(inner[1]).bit_length()}, peak {max(ranks_inner)}, equality rank {max(e[1]).bit_length()}, wrapped output verified')
if __name__=='__main__':
    for size in range(1,7):
        structural_controls(size)

def encrypt(half, gates, message):
    n = 1 << half
    one = ([1] * n, [1] * n)
    wires = [one]
    for side in range(2):
        for i in range(half):
            bit = [(a >> i) & 1 for a in range(n)]
            wires.append((bit,one[1]) if side==0 else (one[0],bit))
    output = one
    for a,b in gates:
        read = lambda j: wires[j] if j<len(wires) else one
        output=nand(read(a),read(b))
        wires.append(output)
    return message & int(any(output[1]))

def scalar(bits,gates):
    wires=[1]+list(bits)
    out=1
    for a,b in gates:
        read=lambda j: wires[j] if j<len(wires) else 1
        out=1^(read(a)&read(b))
        wires.append(out)
    return out

if __name__=='__main__':
    for gs in itertools.product(itertools.product(range(5),repeat=2),repeat=2):
        sat=any(scalar(x,gs) for x in itertools.product(range(2),repeat=2))
        for msg in (0,1):
            assert encrypt(1,gs,msg)==(msg & sat)
    assert encrypt(1,[],1)==1
    print('625 registered-format two-input/two-gate circuits: both message bits passed; empty list passed')

~~~
