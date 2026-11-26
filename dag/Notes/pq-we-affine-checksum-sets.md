---
title: Affine restrictions for comparing path-checksum sets
refs: [note:pq-we-checksum-prefix-keys, note:pq-we-path-checksum-masks]
tags: [witness-encryption, coding, correctness, compression]
---

Retain the previous common boundary vertex and checksum address in GF(2)^d. Suppose the reachable addresses on each side have explicit representations as unions of nonempty affine spaces. The left and right directions may be entirely different. The following masks operate directly in their given coordinates.

For a single pair A=a+U and B=c+V draw a uniform affine Boolean function f(x)=l.x+t on the whole address space. Send the coefficients of f restricted to A and of f+b restricted to B in their *respective local bases*. This uses dim U + dim V + 2 bits when both bases and offsets are public. For example, the first restriction is (f(a), l.u_1,...,l.u_dimU). A witness with common address x derives its coordinates in both bases by linear elimination, evaluates the restrictions and XORs them to obtain b exactly. Neither side needs a common coordinate tree, and each restriction can be formed using just its own flat and the common random coins.

On disjoint flats, c-a is outside U+V. Choose a linear functional vanishing on U+V and taking value one at c-a. Translating it to vanish at a gives an affine function h with h|A=0 and h|B=1. Replacing f by f+h bijects the *entire* ciphertext laws for the two messages. Conversely if the flats intersect, their restrictions determine b. This addresses the disjoint m-dimensional spaces in the preceding prefix lower bound with 2m+2 transmitted mask bits, compared with at least 2^m exact prefix entries in one list. If the decoder lacks the bases, transmit or regenerate those descriptions; arbitrary explicit bases cost O(d(dim U+dim V+2)) bits. This comparison concerns exact representations; a sender that tests for intersection first can directly decide this restricted language.

**Unions and preprocessing.** With p left and q right flats use independent f_ij for every pair. A witness selects any pair containing its address. On disjoint unions all pair restrictions hide jointly by independent shifts. Total mask bits are q sum_i(dim U_i+1) + p sum_j(dim V_j+1). Bases are reusable across pairs. Empty lists require no payload on that branch. Across a graph cut one may instead handle each shared vertex separately. To construct lists, start from the singleton origin and translate flats by edge checksums; merge exact duplicates and apply the identity (a+U) union (c+U) = a+span(U,c-a) for distinct parallel flats over GF(2). Each successful merge reduces the list length; a fixed ordering suffices, with no assumption of optimal merging. This dynamic program is polynomial in the graph size and largest intermediate list, including predecessor unions. A one-vertex chain choosing independently between two increments at each level maintains one flat: translate its offset by the first increment and adjoin the difference to its direction basis. Thus the exponential prefix example also admits efficient *construction* of its two one-flat descriptions. With the original random checksum, only a spurious zero path on a false circuit can cause an unintended intersection. The prior bound 2^-lambda transfers unchanged. Large arbitrary unions remain a genuine unresolved cost.

**Why the pair indexing matters for many clauses.** Consider the tempting compact generalization: for parties i=1,...,m choose random affine functions f_i subject to sum_i f_i being the constant b, and send evaluations/restrictions of f_i on its allowed set S_i. A common point decodes. Nonempty sets yield identical laws for the two bits exactly when their affine hulls have empty intersection. Indeed affine functions vanishing on S_i are precisely the linear span of the affine equations defining its hull. A mask shift requires functions h_i vanishing on S_i whose sum is one. This is exactly the elimination certificate that the combined hull equations are inconsistent. If x is in every hull, the received evaluations extend uniquely on each hull, hence b can be read at x even when x belongs to none of the original intersections.

Take the four two-variable clauses that separately forbid 00,01,10,11. Each clause allows three points and these span the full binary plane. The full formula has no satisfying assignment. The four restricted affine functions nevertheless recover the bit for every choice of masks. This example isolates the gap for a compact clause-wise construction: affine restrictions lose the distinction between a union and its hull. Enumerating every combination of local flats retains it at multiplicative cost. No computational hardness claim or general CircuitSAT compression follows from the pair protocol.

The listing enumerates all nonempty flats of the binary three-dimensional space and every affine mask. It checks equality of message laws exactly for disjoint flats, and disjoint supports for intersecting flats. Evaluations on all points are equivalent to coefficients in a local affine basis.
~~~python
from collections import Counter
from itertools import product
zero=frozenset({0})
spaces={zero}
for v in range(1,8):
    spaces |= {s|frozenset(x^v for x in s) for s in spaces}
flats=sorted({tuple(sorted(x^a for x in s)) for s in spaces for a in range(8)})
def value(key,x):
    return ((key&x).bit_count() + (key>>3))%2
for A,B in product(flats,repeat=2):
    def law(b):
        return Counter(tuple(value(k,x) for x in A)+
                       tuple(value(k,x)^b for x in B) for k in range(16))
    p,q=law(0),law(1)
    if set(A).isdisjoint(B):
        assert p==q
    else:
        assert set(p).isdisjoint(q)
for omitted in range(4):
    allowed=set(range(4))-{omitted}
    a,b,c=allowed
    assert a^b^c==omitted
print(len(flats),len(flats)**2)
~~~
