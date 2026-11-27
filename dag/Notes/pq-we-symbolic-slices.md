---
title: Sharing row masks across affine slices with Boolean polynomials
refs: [note:pq-we-rectangular-boolean-moments, note:pq-we-affine-certificate]
tags: [witness-encryption, correctness, compression]
---

Write the split verifier as M(z)v=s(z), where z is the t-bit selector label and M,s have affine Boolean-polynomial entries. Include consistency of z with v in the system when required by the compiler. For a real witness the label and a solution v are available. The previous erasure construction emits a separate slot per label. Here the sender can emit one symbolic slot and the receiver evaluates it at its own z.

Work in the Boolean ring GF(2)[z]/(z_i^2-z_i). Fix a publicly indexed set of squarefree monomials B_i for each equation i. Independently sample fair coefficients of a_i from the span of B_i. Publish the coefficient vectors of

    C = M^T a,       T = b + s^T a.

Lists of possible output monomials, including the constant of T, are public and fixed before sampling. Merge equal monomials by XOR and transmit the zero coefficients too. In particular transmitting unmerged terms or the circuit which computes them could reveal the masks. Given a witness, evaluate T(z)+v^T C(z) to recover b exactly. With N mask coefficients and E public monomial products before merging, the size is at most E+1 bits, with polynomial generation and evaluation in E, the system dimensions and t. No full cube table is needed when the named supports are small.

**Exact criterion.** In coefficient coordinates the law is uniform on a binary linear subspace translated by the message bit times the public tag vector e. The two laws coincide iff there is a vector of Boolean polynomials d_i in the respective named spans such that

    M^T d = 0,       s^T d = 1    as identities in the Boolean ring.

A successful shift translates the mask coefficients bijectively. Conversely disjoint affine cosets are perfectly distinguished by a linear functional obtained by solving a public linear system. This is a statement about the entire published transcript, not just a single evaluation. On any true instance such a shift is impossible, by evaluating at a valid z and multiplying by v. On any false instance, *unrestricted* functions d exist by choosing a left nullvector with nonzero pairing with s on each inconsistent slice. The full Boolean function space represents every such choice; what matters for compression is a small common coefficient representation with correct identities. If the compiler always produced polynomial lists that admitted these shifts on all false circuits, public elimination would decide CircuitSAT in polynomial time. This criterion also explains why replacing the fair coefficients by a pseudorandom generator alone cannot fix a missing shift: the same linear functional reads b for every coefficient vector.

**A finite-cost separation between degree and support.** Consider the t-selector chain y0=0, y_i+z_i y_(i-1)=0 for i=1,...,t, y_t=1. All slices are inconsistent. Write d_0 for the first row, d_1,...,d_t for transitions, d_* for the last row. The tag forces d_*=1; then d_t=1, d_(i-1)=z_i d_i. Thus d_i=S_i=product_(j=i+1)^t z_j in the unique shift. In particular a uniform cutoff below t on all degrees completely leaks b, since S_0 has multilinear degree t. Conversely a *single* allowed monomial S_i per row and the constant for d_* suffice. Writing the random scalars as A_i,A_*, the emitted values are t+1 coefficients A_i+A_(i+1) (with A_(t+1)=A_*), followed by A_*+b. Each of the first t+1 coefficients multiplies the known S_i in C_i. There are exactly t+2 bits and the distribution is uniform for either b: for fixed b the coefficient map is invertible by backward substitution. The suffix names are implicit and the receiver can evaluate them all in O(t) operations. This explicit unsatisfiable family demonstrates mask compression rather than hardness or a nontrivial SAT algorithm.

More generally for a layered affine transition y_i=A_i(z)y_(i-1), y_0=0 and terminal condition l^T y_t=1, the dual transition is d_t=l and d_(i-1)=A_i(z)^T d_i (last-row shift one). The same calculation gives an algorithm: recursively multiply in the Boolean ring, XOR duplicate monomials, and use the resulting supports per row. Its cost depends on the intermediate supports as well as the final one. Sparse transition matrices do not ensure sparse responses: with scalar transitions 1+z_i the first response is product_i(1+z_i) with 2^t distinct squarefree monomials. Complementing the selector coordinates makes this particular example sparse again. No representation bound for arbitrary circuits follows.

The check builds the actual coefficient map for the chain, independently searches for the tag in its column span by elimination, and exhausts the two message laws with the singleton supports. It checks all uniform degree cutoffs, with the full degree-t basis giving the positive control.
~~~python
from collections import Counter
from itertools import product

def build(t,bases):
    columns=[]
    for i,B in enumerate(bases):
        for m in B:
            if i==0: col={(0,m)}
            elif i==t+1: col={(t,m),(t+1,m)}
            else: col={(i,m),(i-1,m | (1<<(i-1)))}
            columns.append(col)
    return columns

def contains(columns,e):
    pivots={}
    def reduce(v):
        while v and max(v) in pivots:
            v=v ^ pivots[max(v)]
        return v
    for col in columns:
        v=reduce(col)
        if v: pivots[max(v)]=v
    return not reduce(e)

for t in range(1,8):
    tag={(t+1,0)}
    for D in range(t+1):
        basis=[m for m in range(1<<t) if m.bit_count()<=D]
        assert contains(build(t,[basis]*(t+2)),tag)==(D==t)
    suffix=[[(1<<t)-(1<<i)] for i in range(t+1)]+[[0]]
    columns=build(t,suffix)
    assert contains(columns,tag)
    counts=Counter()
    for coeff in product(range(2),repeat=t+2):
        value=set()
        for bit,col in zip(coeff,columns):
            if bit: value ^= col
        counts[frozenset(value)]+=1
    assert len(counts)==1<<(t+2)
    assert all(counts[v^tag]==n for v,n in counts.items())
print("35 degree cutoffs and 7 complete law comparisons")
~~~
