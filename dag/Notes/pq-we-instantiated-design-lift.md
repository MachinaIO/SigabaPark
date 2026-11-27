---
title: Separate ordinary-LWE and tensor dimensions for the prefix-tree design switch
refs: [definition:WE_CircuitSAT, note:pq-we-quantum-prefix-tree, note:pq-we-digit-secret-trapdoor, note:pq-we-stage-gap-search]
tags: [witness-encryption, reduction, sampling, complexity]
---

The previous compact parameter searches took the short Gaussian design in an isolated prefix tree as an assumption. The earlier tree note gave a reduction to uniform-design LWE if one can sample suitably short conditioned columns. Here the digit trapdoor supplies that sampler with distinct base and tensor dimensions, and we price the resulting expansion. This substitutes for the isolated-tree design assumption, not for the root PRE-to-POST evasive-LWE premise.

**One level.** Start with uniform U of shape d0 by M over Z/q and a multi-secret challenge Y=T U+E or uniform, where M=B_i n for B_i branches. Generate an independent private trapdoor for a public H of shape d0 by n. For each U column sample a length-n discrete Gaussian of width n conditioned on H p=U_col, forming P. Use independent masks W with n entries per row of Y. Output P and Y+WP. On the LWE side the new secret TH+W is uniform independently of the conditioned design, old secrets and errors. On the uniform side the response remains uniform. All B_i transposed square tensor blocks are obtained from the one common P. Use a hybrid over the parent secrets sharing U to charge ordinary one-secret hardness at M samples. In particular one cannot use the larger tensor dimension as the base LWE hardness dimension.

**Exact endpoint cost.** For a fixed surjective H let mu be the iid Gaussian column law, D its syndrome marginal, and nu the mixture of the same conditional columns over uniformly selected syndromes. Since fibers are disjoint, TV(mu,nu)=TV(D,uniform) exactly. The trapdoor is surjective even on atypical keys. With M independent columns the distance for fixed H is at most M times this single-column distance. The additional output responses are a common randomized channel of P on each endpoint, so this term is independent of the number of parent secrets. For uniform H the character bound in the digit note gives E Delta <= 2^-b when flatbits >= b in the listing; TV(D,uniform)<=Delta/2. Transfer the bounded M-column distance to the real trapdoor public marginal with one key-distance charge. Then add at most M times the bounded conditional sampler distance. Both real and uniform endpoint switches must be counted. At precision b=2K for the inner keys and preimages the sum is at most (3M+2)2^-b. The control budgets up to three such levels per isolated prefix estimate, in addition to the ordinary hybrid terms. Scalar approximations elsewhere in the tree and inside the root reduction still need their original weighted budgets.

**Dimensions.** Put q=2^K and d0=K² for the conditional 2^K-time, 2^-K-advantage ordinary *quantum* LWE envelope. Build an inner digit trapdoor at rank d0, with its public width determining n. Require n²>=V(2K+ceil(log2 n)+4), where V is the inner squared Gram-Schmidt bound. Thus the desired factor width n is sufficient for the actual clocked preimage sampler. Check the mean-syndrome estimate with that same width. At the honest interface use a separate trapdoor of rank 24n with gadget exponent and digit entropy six each. Its column width, sampler Gaussian and projected residual are recomputed at the new n. The inner trapdoor is used by the security reduction only; the honest factor law is the iid width-n Gaussian. For fixed small radix and digit size the inner width is polynomial in d0,K: e.g. at binary digits and radix two it grows on the order of K³ for d0=K². Its squared width eventually dominates V times the O(K+log n) smoothing multiplier. Increasing this dimension has real consequences for honest cost.

**Control.** For the (10,4,10) shape and lambda=64, search K=512..3072 with inner radix and secret-digit exponents 1..10. The prior hop-gain exponent is one. Use a wrapper-time exponent of twelve as a *supplied envelope*, which still needs an implementation-level time bound for the full reduction. At 52 of 100 exponent pairs the checks pass; the smallest recorded payload uses K=1235, inner radix 32 and four-bit digits. Its base dimension is 1,525,225; the tensor dimension is 847,645,044. The largest ordinary LWE challenge has 867,988,525,056 samples per secret, and the packed honest payload is 4.6047e28 bits per encrypted bit. The listing prices the first passing K for each pair. This is evidence of numerical compatibility of the indicated inequalities. It neither certifies concrete LWE hardness at the listed parameters nor gives an end-to-end quantum security theorem or a usable parameter set. The earlier compact points did not account for this ordinary-design conversion. A small exact distribution test at q=3 checks the joint law of both output responses and the design at both endpoints; in that example both total variation distances equal the design marginal distance 31/576.

~~~python
from pathlib import Path
from math import isqrt

def lg(x):return (x-1).bit_length()
def cs(x):return isqrt(x-1)+1
def trap(r,K,a,d,prec):
    ell=r*((K+a-1)//a)
    slack=2*(prec+lg(ell))+2
    h=max(r+slack,(r*K+slack+d-1)//d)
    return h+ell,(1<<(2*a))*(h*((1<<d)-1)**2+1)+1

def flatbits(r,K,m,sigma):
    v=sigma.bit_length()-1
    return min(m//2-r,m-2*r-lg(K),m*(v-1)-r*K)-2

def trial(K,a,d):
    base=K*K
    prec=2*K
    n,V=trap(base,K,a,d,prec)
    M=1024*n
    if n*n<V*(prec+lg(n)+4) or flatbits(base,K,n,n)<prec:return None
    r=24*n
    m,Vout=trap(r,K,6,6,70)
    C=16*m+1024*34
    sigma=cs(Vout*(68+lg(C)+lg(m)+4))
    if flatbits(r,K,m,sigma)<74:return None
    scale=2+64+3+24+n+m+K+1024
    L=[lg(scale*p) for p in (1024,16384)]
    gains=[L[0],sum(L)]
    unit=64+lg(64*3)+sum(L)
    simtime=sum(L)+lg(5)+max(64,12*lg(scale*2**24))
    hybrids=24*m*3*2**24
    if K<max(simtime,unit+lg(hybrids)):return None
    if prec<unit+lg(12*M):return None
    moment=2*1024*n*m*2**24*24*(n**3)**3*4*n*n
    f=unit+(lg(moment)+1)//2+sum(max(8,l*lg(1+l),64+lg(192)+g+l)
                                 for l,g in zip(L,gains))
    def z(N):return cs((68+lg(6*N)+3)//4)
    A=z(C*m)*sigma
    scalar=z(2064*(n*n+r*m+n*m))
    residual=scalar<<f
    for i in (1,2):
        residual=m*A*residual+24*(n*n*scalar)**i*scalar*n
    if 16*(residual+1)>1<<K:return None
    bits=min(K,lg(2*A+1))
    return (1024*K*m+bits*m*C,K,a,d,base,n,M,m,sigma,bits)

def main():
    rows=[]
    for a in range(1,11):
        for d in range(1,11):
            for K in range(512,3073):
                out=trial(K,a,d)
                if out:
                    rows.append(out)
                    break
    assert rows
    print("feasible pairs",len(rows),"smallest recorded payload",min(rows))
main()

from fractions import Fraction as F
from itertools import product
from collections import defaultdict
def finite_check():
    q=3
    prob=[F(1,4),F(1,2),F(1,4)]
    vectors=list(product(range(q),repeat=2))
    mu={p:prob[p[0]]*prob[p[1]] for p in vectors}
    syndrome=lambda p:sum(p)%q
    mass=[sum(mu[p] for p in vectors if syndrome(p)==u) for u in range(q)]
    nu={p:mu[p]/(q*mass[syndrome(p)]) for p in vectors}
    assert sum(abs(mu[p]-nu[p]) for p in vectors)==sum(abs(x-F(1,q)) for x in mass)
    for uniform in (False,True):
        actual=defaultdict(F)
        ideal=defaultdict(F)
        for P in product(vectors,repeat=2):
            for W in vectors:
                def action(v):
                    return tuple(sum(x*y for x,y in zip(v,p))%q for p in P)
                for E in vectors:
                    key=(P,E if uniform else tuple((x+y)%q for x,y in zip(action(W),E)))
                    ep=F(1,q*q) if uniform else prob[E[0]]*prob[E[1]]
                    ideal[key]+=mu[P[0]]*mu[P[1]]*ep/(q*q)
                    for secret in range(q):
                        Y=E if uniform else tuple((secret*syndrome(p)+e)%q for p,e in zip(P,E))
                        key=(P,tuple((x+y)%q for x,y in zip(action(W),Y)))
                        actual[key]+=nu[P[0]]*nu[P[1]]*ep/(q**3)
        gap=sum(abs(actual[k]-ideal[k]) for k in actual)/2
        marginal=sum(abs(nu[x]*nu[y]-mu[x]*mu[y]) for x,y in product(vectors,repeat=2))/2
        assert gap==marginal
        print("two-column endpoint TV",gap)
finite_check()
~~~
