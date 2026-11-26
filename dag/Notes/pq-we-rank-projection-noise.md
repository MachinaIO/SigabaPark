---
title: Modular noise in one or several rank-one decoding projections
refs: [note:pq-we-negacyclic-pencil, note:pq-we-short-rank-pencil]
tags: [witness-encryption, rank, correctness]
---

In the negacyclic pencil, worst-case absolute error estimates do not quantify cancellation modulo q. Consider actual iid coefficient noise e_j, each the sum of eta>=1 independent differences of two fair bits. Let d be a power of two, q an odd prime, and alpha_1,...,alpha_b distinct roots of x^d+1 in F_q. Form Z=(e(alpha_i))_i from the degree-<d noise polynomial. For every power-of-two l dividing d with l>=b, the statistical distance from uniform on b field elements satisfies

    TV <= (1/2) sqrt(q^b-1) exp(-pi² eta floor(d/(l b)) q^(-2b/l)).

For b=1 this applies to every rank-one coefficient functional of the full pencil up to a nonzero scalar: the kernel of the bilinear pairing (s,r) -> f(sr) on one side is an ideal, and rank one makes the unital quotient one-dimensional over F_q. Its quotient map is evaluation at a field root, and f is a scalar multiple of that map. Padding missing coefficients by zeros gives the same reasoning for a selected-coefficient pencil. The invertible changes of basis on the inputs from the preceding note preserve this characterization. Distinct evaluation vectors are linearly independent for b<=d by Vandermonde.

**Derivation.** At a nonzero Fourier frequency u in F_q^b, the j-th coefficient is weighted by w_j=sum_i u_i alpha_i^j. Write |w|_q for the centered absolute residue. Since the Fourier factor of one fair-bit difference is cos²(pi w/q) and log(cos x)<=-x²/2 on [0,pi/2), the Fourier modulus is at most exp(-pi² eta sum_j |w_j|_q²/q²).

Set m=d/l and separate indices into m blocks j=a+m t, with 0<=a<m and 0<=t<l. On each block the functional is a sum of at most b evaluations at roots alpha_i^m of x^l+1, with repetitions combined. Its bilinear matrix has rank at most b. For a nonzero block the determinant argument of the preceding note applied in degree l gives squared centered norm at least q^(2-2b/l). To count nonzero blocks, look at the entries w_a for t=0. No b consecutive entries can all vanish: the consecutive Vandermonde system on the distinct nonzero roots would force u=0. Each disjoint group of b consecutive offsets thus contributes at least one nonzero block. Summing their energies and applying finite Fourier Parseval and Cauchy-Schwarz gives the stated bound. For b=1 all m blocks contribute. One can minimize over l and cap the bound at one.

**Decoding consequence.** With t independently sampled rows of error, the full list of these b projections per row is within t times the bound of uniform, even conditioned on all public multiplier rows, the short secret, and a fixed witness independent of the encryption coins. The noiseless signal merely translates each row. In the comparison mode the projections of uniform response rows are exactly uniform by linear independence. Thus any decoder restricted to these public rows and projections has equiprobable-bit success at most (1+min(1,t TV_bound))/2. This conclusion includes nonlinear postprocessing and list tests of the selected projections. Other ciphertext coordinates correlated with the same errors are outside that conclusion. No computational hardness assumption is required for the bound. In particular, for fixed b and polynomial q,t with d growing polynomially faster than log² q, the estimate can be very small (choose l of order b log q within d and account for t). The fixed ring game can hide a transcript yet also erase the projected decoding signal. A proposed construction must supply a different YES geometry or use additional ciphertext information in its decoder.

**Controls.** The listing convolves integer counts modulo q, including a joint two-evaluation law. It also prints optimized analytic projections at a larger arithmetic example. These parameters illustrate the error analysis only.
~~~python
from collections import Counter
from itertools import product
from math import exp,pi,sqrt

def certificate(d,q,b):
    return min((min(1,0.5*sqrt(q**b-1)*exp(-pi*pi*(d//(l*b))*q**(-2*b/l))),l)
               for l in (1<<i for i in range(d.bit_length())) if l>=b)

def check(d,q,roots):
    assert all(pow(a,d,q)==q-1 for a in roots)
    b=len(roots)
    hist=Counter({(0,)*b:1})
    for j in range(d):
        weights=[pow(a,j,q) for a in roots]
        updated=Counter()
        for point,count in hist.items():
            for sign,mult in [(-1,1),(0,2),(1,1)]:
                target=tuple((x+sign*w)%q for x,w in zip(point,weights))
                updated[target]+=count*mult
        hist=updated
    total=4**d
    assert sum(hist.values())==total
    gap=sum(abs(q**b*hist[p]-total) for p in product(range(q),repeat=b))
    tv=gap/(2*total*q**b)
    bound,l=certificate(d,q,b)
    assert tv<=bound+1e-14
    print(d,q,b,tv,bound,l)

check(8,17,[3,5])
check(128,257,[3])
for b in (1,2,4):
    print("analytic",1024,12289,b,certificate(1024,12289,b))
~~~
