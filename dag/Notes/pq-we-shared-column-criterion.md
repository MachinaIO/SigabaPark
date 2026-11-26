---
title: Joint hiding bounds for two-row ciphertexts with a shared private factor
refs: [note:pq-we-two-row-packing, note:pq-we-private-moment-products]
tags: [witness-encryption, reduction, rank, complexity]
---

Use the two-row format with n=s+p columns. For fixed L stack all h matrices L K_i vertically to form A_L. Write V_L=image(A_L) and D for the map taking a two-vector z to the stack of gamma_i z. Every ciphertext column, conditional on L, is an independent uniform point of V_L translated by the corresponding D Z_m column. This single space accounts for every observed block and pilot. For two distinct messages the difference of the two translation matrices Z has row rank two. Define eta=Pr_L[image(D) is not contained in V_L]. Conditional distance is exactly zero on containment and one otherwise, so the unconditional joint distance is at most eta. No exposure of L or independence between blocks is required in this upper bound.

**A sufficient case independent of h.** Change the public moment basis to gamma=(1,0,...,0) when gamma is nonzero. In the common right kernel H of the homogeneous K_i for i>1, suppose K_1 restricted to H has rank r>=2. On that subspace A_L has only its first two rows active, and these span both target coordinates whenever L on K_1(H) has rank two. Hence eta<=1-(1-q^(-r))(1-q^(1-r)), even if the number of homogeneous blocks is arbitrarily large. At gamma=0 all message laws coincide. This proves joint statistical secrecy on a promise without the earlier q^(2nh) Fourier counting penalty. The premise is readily checked by linear algebra. For example a block diagonal family with normalized generator supported on a fresh rank-r block and arbitrary homogeneous generators on the complementary block satisfies it. This example is an abstract pencil, not a compiler for all false statements.

**Dependence on payload length.** Let k_L=dim V_L, a=n-2 and F(k,a) the probability that a independent uniform samples span a given k-dimensional space. It is zero when a<k and otherwise equals the product of (1-q^(j-a)) over 0<=j<k. The joint distance lies in the interval

    E_L[1_bad F(k_L,a)] <= TV <= eta.

In fact the lower bound is an acceptance gap of a polynomial-time subspace membership test. To see the lower bound as a distributional event, subtract the known first translation and change column coordinates by a public invertible matrix so the difference of translations has a zero on its first a columns and its last two columns span image(D) after applying D. Uniform independent preimages for the n columns stay uniform independent under this transformation. Consider the event that the last two vectors belong to the span of the first a. Conditional on good L, both laws coincide. For bad L, the event is impossible in the shifted law, and in the first law its probability is at least F(k_L,a). This proves the claim without giving the observer L. Both data and pilot columns count in a, even if there is only one explicit pilot. For a>=k_max+u with k_max=min(2h,d_R), the line union bound gives F>=1-q^(-u)/(q-1). Thus simply scaling payload length can remove the potential gap between computational secrecy and the public absorption condition. At short lengths the lower bound may be zero and says nothing about computational hiding there.

**Scope of a fixed-game proof.** Every true statement fails absorption for every L: applying its witness coefficients to V_L yields at most the line spanned by L x_left, while applying them to image(D) yields the full two-dimensional space. If every false statement had negligible eta, sampling L and testing containment would give a one-sided randomized decision procedure for UNSAT with overwhelming acceptance on false instances. In the long-payload regime above, security against the efficient test itself forces eta to be negligible when its span probability is bounded below by a constant. This implication concerns this particular encryption format. It gives a reason to keep each use short and use independent coins between uses when pursuing computational rather than statistical security. Repeated short uses still need a proof for one complete short transcript and the usual hybrid loss.

The check exhausts distributions of tiny subspace mixtures in F_2^3. Each sample has four columns, two unchanged and two independently shifted directions. It compares the distance to both bounds using rational arithmetic.
~~~python
from collections import Counter
from fractions import Fraction
from itertools import product

def span(xs):
    values={0}
    for x in xs:
        values |= {v^x for v in values}
    return values

def law(spaces,shift):
    counts=Counter()
    for V in spaces:
        mass=Fraction(1,len(spaces)*len(V)**4)
        for x,y,z,w in product(V,repeat=4):
            counts[x,y,z^shift[0],w^shift[1]]+=mass
    return counts

spaces=[span(rows) for rows in ((1,2),(2,4),(1,),(),(1,2,4))]
P=law(spaces,(0,0))
Q=law(spaces,(1,2))
tv=sum(abs(P[k]-Q[k]) for k in P.keys()|Q.keys())/2
bad=[V for V in spaces if not {1,2}<=V]
eta=Fraction(len(bad),len(spaces))
def full(V):
    return Fraction(sum(span([x,y])==V for x,y in product(V,repeat=2)),len(V)**2)
lower=sum(full(V) for V in bad)/len(spaces)
def event(law):
    return sum(p for (x,y,z,w),p in law.items() if {z,w}<=span([x,y]))
gap=event(P)-event(Q)
assert lower<=gap<=tv<=eta
print(lower,gap,tv,eta)
~~~
