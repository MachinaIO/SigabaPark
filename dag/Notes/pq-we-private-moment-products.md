---
title: Private bilinear moment products and a shift-sensitive rank bound
refs: [note:pq-we-gate-shift-quotient, note:pq-we-gate-moment-noise]
tags: [witness-encryption, construction, rank, complexity]
---

Use the preceding NAND moment compiler over a prime field. Let a_1,...,a_h be a basis of ker Q, and K_i the symmetric matrix with moment coordinates a_i (use both off-diagonal entries as in the compiler). Put gamma_i=(a_i)_00. Choose two independently uniform PRIVATE matrices L and R of shapes u-by-d and v-by-d. Publish just h blocks

    C_i = L K_i R^T + gamma_i Z,

where Z=0 in mode zero and is an independent uniform u-by-v matrix in mode one. Both factors remain with the sender and may be discarded. This is direct encoding in the quotient by the gate masks; no separate random gate masks need be generated. Computing the public basis by elimination, forming the products, and finding witness coordinates are polynomial. Wire cost per bit is huv field elements when the circuit is already available. The receiver derives the same basis deterministically.

**Witness test.** For a satisfying trace x including its constant one, express its moment vector as sum_i c_i a_i. Then sum_i c_i C_i equals (Lx)(Rx)^T+Z. Decode zero for rank at most one. This accepts zero with certainty. In mode one the result is exactly uniform, so false acceptance is [1+(q^u-1)(q^v-1)/(q-1)]/q^(uv); every nonzero rank-one matrix has q-1 factorizations by a pair of nonzero vectors. In particular u=v=2 costs four field elements per basis vector and gives error 1/q+1/q²-1/q³. A polynomial-bit prime of exponential magnitude suffices for negligible error here. The sender and receiver need no list of possible secret evaluations.

**False-instance analysis.** For frequency blocks T_i of shape u-by-v write B(T) for the ud-by-vd block matrix whose (j,l) block is sum_i (T_i)_(j,l) K_i. Orthogonality of additive characters gives the Fourier coefficient of mode zero as q^(-rank B(T)): average over R conditional on L, then count the left nullspace vectors of B(T). The mode-one coefficient is the same if sum_i gamma_i T_i=0 and zero otherwise. For the two exact ciphertext laws P0,P1, Parseval yields

    q^(huv) sum_c (P0(c)-P1(c))² =
        sum_{T: sum_i gamma_i T_i != 0} q^(-2 rank B(T)).

Thus TV <= half the square root of the right side, capped at one. This treats the correlations between all ciphertext entries. Frequencies representing only homogeneous moments cancel exactly, even if their matrices have small rank. If every normalized affine moment in ker Q (constant entry one) has rank >=rho, then every term remaining has a subblock of rank >=rho, by rescaling one nonzero entry of sum_i gamma_i T_i. For gamma nonzero this gives TV <= (1/2) sqrt((q^(huv)-q^((h-1)uv)) q^(-2rho)). If gamma is zero the two laws coincide. For u=v=2, rho>=2h+s gives TV <= q^(-s)/2. This is a restricted statistical guarantee. The rank distribution can give a tighter bound than the minimum. Full statistical hiding on all false circuits with these correctness guarantees would put CircuitSAT in SZK; this calculation does not establish such a compiler. A computational proof beyond the bound must derive security from a fixed game while simulating the correlated homogeneous blocks, rather than assuming the displayed circuit-specific product is pseudorandom.

**Independent finite control.** An abstract two-dimensional quotient over F_2 uses K_1=I_2 and K_2=diag(1,0), gamma=(1,0), u=v=2. Enumerate both ciphertext histograms, and independently compute every binary block rank; check Parseval exactly as an equality of fractions. This checks the product analysis, not a NAND security instance.
~~~python
from collections import Counter
from fractions import Fraction
from itertools import product

def rank(rows):
    basis={}
    for x in rows:
        while x and x.bit_length() in basis:
            x ^= basis[x.bit_length()]
        if x:
            basis[x.bit_length()]=x
    return len(basis)

def blocks(L,R):
    full=first=0
    for j,l in product(range(2),repeat=2):
        pos=2*j+l
        full |= (((L[j]&R[l]).bit_count()%2)<<pos)
        first |= ((L[j]&R[l]&1)<<pos)
    return full,first

p0,p1=Counter(),Counter()
for L in product(range(4),repeat=2):
    for R in product(range(4),repeat=2):
        a,b=blocks(L,R)
        p0[a,b]+=1
        for z in range(16):
            p1[a^z,b]+=1
gaps=[Fraction(p0[c],256)-Fraction(p1[c],4096) for c in product(range(16),repeat=2)]
lhs=256*sum(g*g for g in gaps)
rhs=0
for A,B in product(range(1,16),range(16)):
    rows=[]
    for j,i in product(range(2),repeat=2):
        row=0
        for l in range(2):
            entry=((A^(B if i==0 else 0))>>(2*j+l))&1
            row |= entry<<(2*l+i)
        rows.append(row)
    rhs+=Fraction(1,4**rank(rows))
assert lhs==rhs
print("scaled squared distance",lhs,"TV",sum(map(abs,gaps))/2)
~~~
