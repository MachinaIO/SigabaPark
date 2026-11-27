---
title: Polynomial-size clause addresses with bounded-query perfect hiding
refs: [note:pq-we-clause-key-sum, note:pq-we-clause-subtree-rekey]
tags: [witness-encryption, coding, reduction, correctness]
---

Use the preceding rounded clause-share template, with prime h>=3, p=h^a and q=ph. Fix a public polynomial-basis presentation of GF(h^k) where h^k>=2^n. Interpret each n-bit string injectively as an extension-field element x via base-h digits. For a chosen integer D between 1 and 2^n construct the address row A(x) by concatenating 1 and the k coordinates of each x^j for 1<=j<D not divisible by h. Lift the base-field coordinates as integers in [0,h-1] into Z/q. Length is d=1+k(D-1-floor((D-1)/h)). The address is independent of the formula. Its computation takes O(D) extension-field multiplications plus polynomial coordinate work. This uses the Vandermonde and Frobenius checks underlying [BCH codes](https://cse.buffalo.edu/faculty/atri/courses/coding-theory/spr09/lectures/lect24.pdf).

**All sets of at most D addresses are independent modulo h.** A base-field dependence on l<=D distinct addresses would give sum_i c_i x_i^j=0 for each kept exponent and j=0. Raising to the h-th power recovers every omitted multiple of h, recursively. The square Vandermonde system on exponents 0 through l-1 is invertible, so all coefficients vanish. Some l-by-l minor is therefore a unit modulo the prime power q. A uniform K in (Z/q)^d gives *jointly uniform* raw phases at all l points. Also any relation expressing A(w) as a signed integer combination of other addresses modulo q must use at least D distinct other addresses with coefficients nonzero modulo h. In particular the former 15-point interpolation cannot apply for D>=16. The leading one guarantees the primitive-row condition of the rounding analysis.

**Joint security at a specified query budget.** Freeze any set of at most D addresses on a false formula. In the independent-key experiment all m-by-l phases are independent uniform residues. In the zero-sum experiment take the first m-1 keys uniform and the last minus their sum. The columns of raw phases are then independent, each uniform subject only to its sum being zero. At each address at least one clause forbids evaluation. Projection of a uniform zero-sum column onto *any proper subset* of entries is exactly uniform, including when the omitted clause differs between columns. Thus the allowed phases, even all allowed phases at once per address, have identical joint laws in the two experiments. Applying the same rounding maps preserves equality conditional on the public dithers. This covers adaptive classical evaluation at at most D distinct addresses by matching transcript probabilities. It also covers T quantum queries for 2T<=D to the reversible oracle returning the entire vector of allowed rounded answers with a fixed marker for each forbidden position. Each final acceptance probability expands in products of at most 2T oracle-entry indicators by induction on query amplitudes and squaring; the two experiments agree on every such joint moment. There is no query restriction on genuine witness *computation* to form the one address at which the shares are added.

**Costs and limits.** The honest threshold and bounds from the preceding note apply with the new q,p,h. For m=4097, h=3, p=2187 and eta=1/32, the zero-message failure bound is 1/32 and the independent-key failure bound is below 0.15. For an illustrative n=4096 and D=32, k=2585 and d=54286; increased query coverage costs master-key coordinates. These are symbolic bounds for authorized evaluation, not public ciphertext sizes. A fixed polynomial D does not cover every polynomial-query adversary. More importantly, supplying restricted *key strings* gives the receiver information in addition to their authorized values. Neither their generation nor their joint security follows from this coding lemma. Increasing D, or regarding the oracle as a reusable public circuit, does not establish general WE. The prime-power choice is used for joint uniformity; a minor invertible only mod h need not be invertible mod a composite q with other prime factors.

The check uses GF(9)=GF(3)[i]/(i^2+1) and q=9. It checks every set of four addresses with the Frobenius exponent three omitted, then exhausts a full lifted phase law for three addresses at D=3. It also computes the numerical witness bound.
~~~python
from itertools import combinations,product
from collections import Counter
from math import sqrt,log
def row(x):
    a,b=x
    return (1,a,b,(a*a-b*b)%3,(2*a*b)%3)
def independent(rows):
    piv={}
    for r in rows:
        v=list(r)
        for j in sorted(piv):
            c=v[j]
            v=[(a-c*b)%3 for a,b in zip(v,piv[j])]
        j=next((i for i,a in enumerate(v) if a),None)
        if j is None: return False
        piv[j]=[(a*pow(v[j],-1,3))%3 for a in v]
    return True
rows=list(map(row,product(range(3),repeat=2)))
assert all(independent(group) for group in combinations(rows,4))
points=(rows[0],rows[4],rows[8])
counts=Counter(tuple(sum(a*b for a,b in zip(r,key))%9 for r in points)
               for key in product(range(9),repeat=5))
assert len(counts)==9**3 and set(counts.values())=={9**2}
m,h,p,eta=4097,3,2187,1/32
T=(h-1)*sqrt(m*log(2/eta)/2)
print(len(list(combinations(rows,4))),len(counts),eta+(4*T+1)/(p*h))
assert 3**2584<2**4096<=3**2585
assert 1+2585*(31-31//3)==54286
~~~
