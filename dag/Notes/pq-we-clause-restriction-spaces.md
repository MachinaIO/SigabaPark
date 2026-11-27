---
title: Computing exact clause restrictions of nonlinear indicator masks
refs: [note:pq-we-affine-checksum-sets, note:pq-we-symbolic-slices]
tags: [witness-encryption, construction, compression, correctness]
---

For a CNF on n bits and m>=1 clauses let U_i be the subcube of inputs violating clause i and let S_i be its complement. Normalize repeated literals; tautologies have empty U_i and the empty clause has full U_i. Choose s public features Phi(x) consisting of the constant one (index 0) and indicators of specified subcubes. Each feature is a product of coordinate tests, including complements. Its value on a supplied witness costs O(n) bit tests even when its algebraic normal form has exponentially many monomials.

**Compute each local mask without listing assignments.** Let V_i be the binary row span of Phi(x) over x in S_i. Initialize a length-s row of ones for the empty prefix and a flag recording whether clause i is satisfied so far. Process the bits in fixed order. Extending with bit b zeros each feature coordinate that excludes b at this position, a public diagonal linear map. Update the clause flag by OR with satisfaction of an encountered literal. For each new flag take a basis of the union of the two-bit extensions from the predecessor flag spaces. Induction on the prefix length proves equality with the span of all reachable rows for that flag: each transition is linear and depends only on position, flag and bit. Keep the accepting flag at the end. Handle tautologies with an initially true flag. Each space has rank <=s. Ordinary elimination costs O(m n s^3) bit operations up to indexing overhead, and O(s^2) streaming working bits per clause apart from stored outputs and feature descriptions. This deterministic calculation performs no probabilistic identity tests.

Sample uniform vectors a_i in GF(2)^s subject to sum_i a_i=b e0. The ciphertext sends a_i dotted with each vector of a canonical basis of V_i. If both parties know the formula and feature rule, no basis descriptions are needed. A valid x has Phi(x) in every V_i. Express it in each basis and XOR the corresponding observed bits: the sum is b. Payload is exactly sum_i dim(V_i) <= ms bits and both algorithms are polynomial in n,m,s. The criterion for identical laws is e0 in sum_i V_i^perp. A decomposition into that sum translates the global masks while fixing every local output; otherwise a vector in the intersection of all V_i pairs to one with e0 and explicitly reads b. This is an exact criterion even if the feature functions themselves are linearly dependent.

**A family of dictionaries with guaranteed NO coverage.** Include the indicators of all distinct nonempty intersections of nonempty collections of the violation subcubes U_i (including any singleton collection with nonempty U_i). Start from the full cube and iteratively intersect the accumulated dictionary with the next U_i, drop empty results and merge identical literal patterns. Intermediate sets persist, so cost is O(mns) with hash tables in expected dictionary time. The all-input OR of the violation indicators equals their inclusion-exclusion sum over GF(2): for a point in j>0 of them the parity is (2^j-1) mod 2 = 1. Each summand is zero or a named intersection indicator, and vanishes throughout at least one S_i. Group identical indicators by parity and assign each surviving one to a clause whose violation cube contains it. On NO their sum is pointwise one. Any discrepancy between this coefficient sum and e0 is a globally zero function and can be added to the first local shift. This supplies the required decomposition and gives perfect hiding. The proof need not enumerate subsets to run Enc or Dec.

If any point can violate at most t clauses, s<=1+sum_{j=1}^t binom(m,j). The exact number of distinct intersections can be much smaller because different subsets can describe the same subcube. For the prefix partition by the first bit equal to one, plus the all-zero point, m=n+1 disjoint violation cubes cover the domain. There are s=m+1 features including the constant, and each local rank is m-1: on S_i the m-1 possible distinct rows are a constant coordinate followed by distinct unit vectors. The one-bit payload is m(m-1). The all-zero indicator alone would have 2^n monomials in expanded Boolean normal form. The same construction repairs the four-clause counterexample of the preceding note using 12 mask bits.

There are also false instances with exponentially many distinct intersections: include n unit clauses x_i and an extra clause negating x_1. Even the intersections among the original violation cubes alone give 2^n-1 different nonempty sets. Simplification can decide this example, but the literal closure-size guarantee for arbitrary formulas is exponential. A uniform polynomial-size dictionary with the shift on every NO instance would give a polynomial SAT test by the same span criterion. A reduction from a fixed computational assumption for NO instances outside a small dictionary's coverage remains open.

The check compares the flag-space computation to exhaustive evaluation and checks the exact hiding criterion against satisfiability, on 200 seeded small CNFs with the full intersection dictionary.
~~~python
from itertools import product
from random import Random
rng=Random(31)
def basis(vectors):
    piv={}
    for row in vectors:
        while row and row.bit_length() in piv:
            row ^= piv[row.bit_length()]
        if row: piv[row.bit_length()]=row
    return tuple(piv.values())
def allowed(cube,x): return all(x>>j&1==b for j,b in cube)
def span(rows):
    out={0}
    for r in rows: out |= {x^r for x in out}
    return out
for _ in range(200):
    n=rng.randrange(1,5)
    cubes=[frozenset((j,rng.randrange(2)) for j in range(n) if rng.randrange(2))
           for _ in range(rng.randrange(1,7))]
    features={frozenset()}
    for u in cubes:
        features |= {v|u for v in features if len(dict(v|u))==len(v|u)}
    F=sorted(features,key=lambda u:(len(u),sorted(u)))
    common=None
    for u in cubes:
        states=[((1<<len(F))-1,),()]
        for j in range(n):
            dest=[[],[]]
            for flag,b in product(range(2),repeat=2):
                mask=sum(1<<i for i,v in enumerate(F) if (j,1-b) not in v)
                dest[flag or (j,1-b) in u].extend(r&mask for r in states[flag])
            states=list(map(basis,dest))
        actual=span(states[1])
        explicit=span(basis(sum(1<<i for i,v in enumerate(F) if allowed(v,x))
                            for x in range(1<<n) if not allowed(u,x)))
        assert actual==explicit
        common=actual if common is None else common & actual
    sat=any(all(not allowed(u,x) for u in cubes) for x in range(1<<n))
    assert sat==any(r&1 for r in common)
print("200 CNFs")
~~~
