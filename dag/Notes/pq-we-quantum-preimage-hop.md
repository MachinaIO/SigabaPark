---
title: A classical-input quantum reduction for the transition-preimage hybrid
refs: [definition:WE_CircuitSAT, note:pq-we-fixed-budget-vww, note:pq-we-ordered-radix-gadget]
tags: [witness-encryption, reduction, complexity, lwe]
---

**Scope.** Step 2 of [VWW Lemma 5.2](https://ntt-research.com/wp-content/uploads/2023/01/Witness-encryption-and-null-iO-from-evasive-LWE.pdf) removes pairs of transition-preimage matrices after the root has been replaced by uniform. [CVW Lemmas 3.10, 3.13, 3.14 and 4.4](https://www.iacr.org/archive/crypto2018/10993366/10993366.pdf) use short public LWE matrices and split trapdoors in this step. Here is a direct classical randomized wrapper for an ordinary *uniform-public-matrix*, uniform-secret decisional-LWE challenge, allowing different preimage and error widths. It runs the putative quantum distinguisher once on a classical string. It neither queries it in superposition nor rewinds it. This addresses the removal of transition matrices; the induction replacing the real root uses an additional assumption.

**One experiment.** Let r be the syndrome dimension, d the ordinary LWE dimension, m=m1+m2 the preimage length and l the number of columns (2m for two concatenated square transition blocks). Fix q and the target matrix Z of shape r by l, possibly jointly generated with classical auxiliary information independent of the key being removed and the LWE challenge. The hidden public key A here is not supplied to the observer. Compare preimages of Z+E under A, drawn with width s, to independent discrete Gaussian columns of width s. Entries of E use the challenge error distribution. The observer may see the auxiliary information, including Z. The condition on hiding A is important: the wrapper below need not know its left block in the real experiment.

**Wrapper.** Receive U uniform in (Z/q)^(d by l) and Y either S U+E with uniform r by d secret S or uniform independent of U. Generate an independent d by m1 trapdoor matrix H, and use its trapdoor to sample each column of D1 from the width-s Gaussian conditioned on H D1 = U. Generate a second independent r by m2 trapdoor matrix A2. Draw W uniform of shape r by m1 and compute T=Z+Y+W D1 modulo q. Sample D2 as a width-s Gaussian preimage of T under A2. Give (D1 stacked above D2, aux) to the observer. Independent randomness is used for each conditional column draw. A zero-oracle classical simulation produces these registers before the final quantum computation.

* Real Y: T=Z+E+(S H+W)D1. Algebraically set A1=-(S H+W); it is uniform and independent of H,S,D1,E,A2 and aux by the uniform mask. The sampler for D2 therefore receives exactly the residual syndrome Z+E-A1 D1. A1 is never needed as an algorithmic output. The only remaining switches are statistical: D1 has the Gaussian marginal up to the smoothing error, and the split sampler for [A1|A2] has the full preimage law up to its own smoothing error.
* Uniform Y: T is uniform independent of D1,A2 and aux, even for singular D1 or repeated columns. Smoothing for A2 makes D2 close to independent Gaussian columns. Smoothing for H does the same for D1.

For the actual VWW use, sample the next key with its trapdoor, the two tensor factors and the remaining suffix, independently of the challenge. Set Z to the horizontal concatenation of the two factor-times-next-key targets. Earlier transitions must already be independent Gaussian in this forward hybrid. The suffix may depend on the next key and factors; their joint distribution with Z is preserved.

**Statistical accounting.** For a good surjective matrix B and a width-s unconditioned Gaussian X, suppose its syndrome law has max/min point-probability ratio at most R_B. The uniform-syndrome lift differs from X in total variation by at most R_B-1: both experiments use the same conditional law given the syndrome. In the real split experiment the correct marginal of a Gaussian first block x conditioned on a fixed overall target t is tilted by Pr[A2 X2=t-A1 x]. Normalizing a tilt with pointwise ratio at most R_A2 changes its law by at most R_A2-1. Conditional on x the second-block laws coincide exactly. These bounds are uniform over targets and persist for correlated Z. With independent columns, a union bound over l applies. Thus the two endpoint switches together cost at most 2l[(R_H-1)+(R_A2-1)], plus bad-key, public-key replacement and finite sampler errors for the two experiments. A nonzero dual mass at most epsilon<1 gives R<=(1+epsilon)/(1-epsilon) for a surjective key by Poisson summation; quantitative advantage requires correspondingly small epsilon. A constant smoothing ratio sufficient for an output-length tail is generally insufficient here.

**Time, samples and assumptions.** Replacing r independent secret rows by uniform one at a time costs at most r times the advantage against ordinary one-secret decisional LWE with l samples. Other rows can be sampled from their real or uniform laws using the same public challenge U. The reduction prepares two keys, l first-block lifts and l second-block draws plus matrix arithmetic, then calls the distinguisher once. Any computational guarantee must pay these costs and the hybrid losses across the H-1 positions. A convenient sufficient allocation for the two trapdoors with logarithm base two is m1>=2d ceil(log q) and m2>=2r ceil(log q), plus any margins required by the particular trapdoor and smoothing bounds. For example at d=32, r=256 and a 128-bit radix length these thresholds total 73728 columns, versus 131072 if both halves were allocated for rank 256. This is an allocation comparison for this reduction, not a claim that the smaller total automatically matches the parameters of the full security theorem. All key dimensions, sampler widths and trapdoor statistical errors must be matched before applying it to an implementation. The explicit proof quantifies over quantum distinguishers of classical samples and assumes quantum hardness of the stated uniform-matrix LWE experiments.

**Remaining proof obligations.** In VWW Step 1 the logical implication from a PRE-game bound to a POST-game bound invokes evasive LWE. Closing Step 2 alone does not yield that implication. A complete PQ proof still needs a justified quantum-adversary premise for the particular sampler family and its auxiliary information, the prefix-product pseudorandomness of Lemma 5.3 at the required time/advantage scale, and control of the losses under all H iterations. The registered classical WE machine game would additionally need an appropriate quantum interface. No PQ evasive-LWE assumption has been registered here, and the 161 MB correctness benchmark is not certified by this result.

**Exact checks.** Enumerating the uniform mask, secret and error alternatives in 36 tiny matrix experiments checked the masked real and uniform target distributions, including repeated and rank-deficient columns and composite modulus. A second check verified the split conditioning tilt for each target in three small cyclic groups. The algebra and statistical bounds above apply to general dimensions; these checks do not test hardness.

~~~python
from collections import Counter
from fractions import Fraction as F
from itertools import product

def pmf(pairs):
    out=Counter()
    for value,prob in pairs:
        out[value]+=prob
    return out

def simulate(q,H,P,uniform):
    # One row, two correlated challenge columns, two short coordinates.
    m=len(H)
    us=[sum(x*y for x,y in zip(H,col))%q for col in P]
    direct=Counter();wrapped=Counter()
    res=list(product(range(q),repeat=m))
    ys=list(product(range(q),repeat=2)) if uniform else [(0,1),(1,0)]
    for mask in res:
        for s,y in product(range(q),ys):
            v=y if uniform else [(s*u+e)%q for u,e in zip(us,y)]
            wrapped[tuple((z+sum(x*w for x,w in zip(col,mask))+i)%q
                          for i,(z,col) in enumerate(zip(v,P)))]+=1
            target=y if uniform else [(e+sum(x*w for x,w in zip(col,mask)))%q
                                      for col,e in zip(P,y)]
            direct[tuple((v+i)%q for i,v in enumerate(target))]+=1
    assert direct==wrapped

def split(q):
    # Fixed target and A1=A2=[1]. Verify the exact conditioning tilt.
    g=[F(i+1,q*(q+1)//2) for i in range(q)]
    ratio=max(g)/min(g)
    for t in range(q):
        weights=[v*g[(t-x)%q] for x,v in enumerate(g)]
        total=sum(weights)
        cond=[v/total for v in weights]
        assert all(1/ratio<=p/x<=ratio for p,x in zip(cond,g))
        joint=pmf((((x,(t-x)%q),prob) for x,prob in enumerate(cond)))
        assert sum(joint.values())==1
count=0
for q in (2,3,4):
    split(q)
    for H in [(0,1),(1,1)]:
        for P in [[(0,1),(1,0)],[(1,1),(1,1)],[(2,0),(1,2)]]:
            for uniform in (False,True):
                simulate(q,H,P,uniform);count+=1
print(count,'exact masked experiments')
~~~
