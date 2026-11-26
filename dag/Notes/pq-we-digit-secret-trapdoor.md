---
title: Shorter dyadic gadget keys from multibit trapdoor entries
refs: [definition:WE_CircuitSAT, note:pq-we-sampler-backed-endpoints, note:pq-we-uniform-syndrome-caps, note:pq-we-ordered-radix-gadget]
tags: [witness-encryption, sampling, complexity, correctness]
---

Keep the gadget public matrix [U | G-UR] modulo q=2^K, but draw each entry of R independently and uniformly from the D=2^d consecutive digits starting at zero. U is uniform of shape r by h. Increasing d reduces the entropy-driven minimum height h, while increasing the width of the backward Gaussian sampler. Over a power-of-two modulus the usual binary collision argument needs modification since differences can have even coordinates.

**Public-key distance.** For two independent digit columns let v be their difference and j its common 2-adic valuation truncated at K. The probability over U that Uv=0 is 2^(-r(K-j)): after dividing out the common power of two some coefficient is odd unless j=K. For 1<=i<=K the probability that every difference is divisible by 2^i equals 2^(-h min(i,d)). Therefore q^r times the mean collision probability of the conditional distribution of UR given U, minus one, is exactly

    sum_(i=1..K) (2^(ri)-2^(r(i-1))) 2^(-h min(i,d)).

For h>r the part through d is at most 2^(-(h-r))/(1-2^(-(h-r))); the rest is at most 2^(rK-dh). By Cauchy-Schwarz and Jensen the mean total variation of one column is at most half the square root of this excess. Put slack=2(b+ceil(log2 ell))+2, and choose h=max(r+slack,ceil((rK+slack)/d)), where ell is the gadget width. The excess is then at most 3 times 2^-slack. Given U the columns are independent, so averaging the conditional product bound gives public-key distance below 2^-b. Translation by G and negation preserve this bound.

**Preimages and concentration.** For radix L=2^a the sheared carry's top coordinates have magnitude at most L(D-1), giving squared Gram-Schmidt bound V=L²(h(D-1)²+1)+1. The last digit relation projects to a vector of length at most L sqrt(h(D-1)²+1), by subtracting earlier carries. After all gadget directions the remaining residual lengths are at most one. Integer lifting and kernel determinant use the same invertible shear as before. Use the preceding bounded backward sampler with integer width ceil(sqrt(V T)), retaining its per-column statistical budget. The number of coins and the bit sizes of intermediate integers remain polynomial at the tested digit sizes, with the same polynomial-clock basis and sampling algorithms.

The reduced m=h+ell can drop below rK. To keep the earlier coordinate tail bound, refine the public uniform-key syndrome calculation. For sigma>=8, put v=floor(log2 sigma). Order-two characters contribute at most 2^(r-m/2). For orders 2^j with 2<=j<=v the scalar divisibility bound is at most 2^(1-j); their aggregate is at most K 2^(2r-m) when m>=r. Higher orders have scalar bound at most 2/sigma, giving total at most 2^(rK-(v-1)m). Require each of these three bounds at most 2^-74 in the control. Twice their sum bounds the bad-key probability before accounting for public-key distance. This recovers uniform conditional tails and signed packing even below the old width cutoff.

**Joint cost.** Retain the (10,4,10) layout, rank r=24 K² and prior full-envelope lower bound. Search a=2..64, d=1..64, recomputing setup width, sampler precision, residual and wire cost at each K. For every pair its first feasible K was found by 1500. At fixed (a,d) the price is nondecreasing with K. The upper-bound comparison per encrypted bit is:

| Choice | K | Gadget radix exponent a | Secret bits d | Key columns m | Bits per transmitted coefficient | Packed bits |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| Previous binary-secret control, same K | 1036 | 4 | 1 | 33358039886 | 29 | 5.1632e23 |
| Multibit, minimum at same K | 1036 | 3 | 3 | 17808127302 | 30 | 1.5222e23 |
| Minimum in new search | 1281 | 61 | 64 | 1615320988 | 147 | 6.1370e21 |

The last point uses 25,845,170,624 sampled columns. It sits on the secret-bit search boundary and has an extremely wide Gaussian. It requires explicit quantum hiding assumptions at its new widths and sample counts; the honest-key distance and polynomial sampler do not prove those assumptions. The result at fixed K is the more direct comparison of the setup change. These numbers are estimates for huge matrices, without full encryption timings. The controls check exact collision equalities on four exhaustively enumerable dyadic instances, check the Gram-Schmidt bounds of three generated bases, and sample all 56 toy target syndromes using the actual clocked sampler.

~~~python
from itertools import product
from fractions import Fraction as F
from functools import lru_cache
from math import isqrt
from random import Random
from pathlib import Path

def listing(slug):
    return Path('dag/Notes/pq-we-'+slug+'.md').read_text().split('~~~python\n',1)[1].split('\n~~~')[0]
ns={'__name__':'planner'}
exec(listing('stage-gap-search'),ns)
@lru_cache(None)
def planner(K):return ns['requirement'](K,[1024,16,1024],24,64,2,'budget')
def lg(x):return (x-1).bit_length()
def ceil_sqrt(x):return isqrt(x-1)+1
def height(r,K,ell,b,d):
    slack=2*(b+lg(ell))+2
    return max(r+slack,(r*K+slack+d-1)//d)
def measure(K,a,d):
    need,(_,n,f,_)=planner(K)
    if K<need:return None
    r=24*n
    ell=r*((K+a-1)//a)
    h=height(r,K,ell,70,d)
    m=h+ell
    if m>2*r*K:return None
    C=16*m+1024*34
    T=68+lg(C)+lg(m)+4
    V=(1<<(2*a))*(h*((1<<d)-1)**2+1)+1
    sigma=ceil_sqrt(V*T)
    # All three order ranges contribute less than 2^-74 separately.
    v=sigma.bit_length()-1
    if min(m//2-r,m-2*r-lg(K),m*(v-1)-r*K)<74:return None
    def z(entries):return ceil_sqrt((68+lg(6*entries)+3)//4)
    bound=z(m*C)*sigma
    scalar=z(2064*(n*n+r*m+n*m))
    residual=scalar<<f
    for i in (1,2):
        residual=m*bound*residual+24*(n*n*scalar)**i*scalar*n
    if 16*(residual+1)>1<<K:return None
    bits=min(K,lg(2*bound+1))
    return (1024*K*m+bits*m*C,K,a,d,m,sigma,bits,C)
def search():
    rows=[]
    for d in range(1,65):
        for a in range(2,65):
            for K in range(1036,1501):
                row=measure(K,a,d)
                if row is not None:
                    rows.append(row)
                    break
    print(len(rows),min(rows),min(x for x in rows if x[1]==1036))
def collisions():
    for K,d,h in ((2,1,2),(3,2,2),(3,2,1),(2,2,2)):
        q=1<<K
        inputs=list(product(range(1<<d),repeat=h))
        total=0
        for u in product(range(q),repeat=h):
            counts=[0]*q
            for x in inputs:counts[sum(a*b for a,b in zip(u,x))%q]+=1
            total+=sum(v*v for v in counts)
        observed=F(total*q,q**h*len(inputs)**2)
        predicted=1+sum(F(2**j-2**(j-1),2**(min(j,d)*h)) for j in range(1,K+1))
        assert observed==predicted

def digit_setup(n,q,b,a,d,bits):
    k=(q-1).bit_length()
    digits=(k+a-1)//a
    base=1<<a
    ell=n*digits
    h=height(n,k,ell,b,d)
    assert q==1<<k
    U=[[bits(k) for _ in range(h)] for _ in range(n)]
    R=[[bits(d) for _ in range(ell)] for _ in range(h)]
    def expand(y):
        return [((v%q)>>(j*a))&(base-1) for v in y for j in range(digits)]
    def shear(u,t):
        return [v+sum(a*b for a,b in zip(row,t)) for v,row in zip(u,R,strict=True)]+t
    def lift(y):
        return shear([0]*h,expand(y))
    cols=[]
    for i in range(n):
        for j in range(digits):
            t=[0]*ell
            if j+1<digits:
                t[i*digits+j]=base
                t[i*digits+j+1]=-1
            elif q==base**digits:
                t[i*digits+j]=base
            else:
                for l in range(digits):
                    t[i*digits+l]=(q>>(l*a))&(base-1)
            cols.append(shear([0]*h,t))
    for j in range(h):
        cols.append(shear([int(l==j) for l in range(h)],expand([-row[j] for row in U])))
    A=[row+[((base**(j%digits) if i==j//digits else 0)-
             sum(row[l]*R[l][j] for l in range(h)))%q for j in range(ell)]
       for i,row in enumerate(U)]
    return A,cols,lift


def draws():
    g={}
    for slug in ('clocked-preimage','ordered-radix-gadget','fraction-free-preimages'):
        exec(listing(slug),g)
    rng=Random(135)
    draw=g['filtered_sampler'](g['sample_squared'],g['threshold'])
    trials=0
    for K,a,d in ((3,2,2),(4,2,3),(5,3,2)):
        q=1<<K
        mat,basis,lift=digit_setup(1,q,4,a,d,rng.getrandbits)
        m=len(basis)
        h=m-(K+a-1)//a
        V=(1<<(2*a))*(h*((1<<d)-1)**2+1)+1
        dirs=g['gram_prepare'](basis)
        assert all(det<=V*prev for _,prev,det in dirs)
        T=8+lg(m)+4
        width=ceil_sqrt(V*T)
        for y in range(q):
            x=g['gram_draw'](basis,dirs,lift([y]),width**2,T-3,rng.getrandbits,draw)
            assert sum(u*v for u,v in zip(mat[0],x))%q==y
            trials+=1
    print("sampled columns",trials)
search()
collisions()
draws()
~~~
