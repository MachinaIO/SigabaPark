---
title: Local verifier tests as erasure information for the fixed syndrome route
refs: [note:pq-we-code-list-features, definition:WE_CircuitSAT]
tags: [witness-encryption, coding, correctness, reduction]
---

In the fixed binary syndrome game, a length-n error e of weight w is independent of the uniform r-by-n matrix H. Consider generating n public local tests, with a genuine verifier test at each support position and an independent decoy elsewhere. The sender knows e and the circuit but needs no witness to generate tests. Suppose every fixed valid witness passes all genuine tests and passes each independent decoy with probability alpha. Crucially, test generation and the resulting set T of passing positions are independent of H conditional on e. Then supp(e) is contained in T and |T| has law w+Bin(n-w,alpha). The receiver needs only this erasure information. Solve H_T z=He by elimination; when H_T has full column rank, extend the solution by zeros to recover e exactly. On deficient rank, report erasure. The random parity bit in the preceding note now requires no additional disambiguating tags.

Conditional on |T|=j the full-rank probability is zero for j>r and otherwise the product of (1-2^(i-r)) over i=0,...,j-1. In particular for any cap c<=r, failure probability is at most Pr[|T|>c]+(2^c-1)2^-r, using the union bound over nonzero kernel vectors. A cap also gives a deterministic polynomial decoder clock. For alpha=1/2, n=2048, w=128, c=1280, r=1408, the exact binomial tail plus the rank bound is below 2^-59. This is a correctness example only; no concrete quantum decoding hardness is assigned to it.

**A concrete correctness experiment and its flaw.** For a NAND circuit choose a random gate's input and output positions and give a predicate on that tuple. At a support position use the prescribed gate output. Else use the same local gate test with an independent fair output flip. Literal gate descriptions give perfect completeness for all satisfying traces and exactly half acceptance for decoys. One may include the final output constraint among the tests using the same flip convention. The flip itself is readable from the circuit and the public predicate: the unflipped positions form a witness-independent set with precisely the erasure distribution above, even on false circuits. Thus this concrete sampler supplies correctness but fails secrecy. Changing the density of decoys cannot correct public visibility of that set.

**Why hiding each local test separately would assume too much.** Suppose a proposed replacement generates a genuine or a decoy with publicly samplable laws. If *these two individual laws* are indistinguishable on false statements and a valid fixed witness accepts them with probability gap at least inverse polynomial, this test pair already gives weak bit WE. For a message bit send independent tests all drawn from the corresponding law. In the perfect-completeness case accept the genuine mode only if all tests pass; the decoy error is alpha^T after T tests. Computational hiding transfers by T ordinary hybrids. This observation pinpoints the noncircular goal: the joint public features need to protect a planted sparse support given its syndrome; separate genuine-versus-decoy hiding cannot be treated as a cheap primitive. Jointly generated tests with correlations require a new bound on |T| and a fixed-game NO simulation. In particular no generic garbling or PCP soundness theorem provides it. The construction has no online verifier or receiver-only hardware.

The listing computes the finite parameter bound using integer arithmetic, and compares the full-rank formula with all small binary matrices, including more surviving columns than rows.
~~~python
from math import comb,prod
from itertools import product
from fractions import Fraction as F

def rank(columns):
    pivots={}
    for v in columns:
        while v and v.bit_length() in pivots:
            v ^= pivots[v.bit_length()]
        if v:
            pivots[v.bit_length()]=v
    return len(pivots)

for r in range(1,4):
    for j in range(5):
        good=sum(rank(columns)==j for columns in product(range(1<<r),repeat=j))
        expected=prod((1<<r)-(1<<i) for i in range(j)) if j<=r else 0
        assert good==expected
n,w,c,r=2048,128,1280,1408
tail=F(sum(comb(n-w,i) for i in range(c-w+1,n-w+1)),1<<(n-w))
bound=tail+F((1<<c)-1,1<<r)
assert bound<F(1,1<<59)
print("tail",float(tail),"erasure bound",float(bound))
~~~
