---
title: A deterministic block gadget for the ordinary-LWE prefix-tree reduction
refs: [definition:WE_CircuitSAT, note:pq-we-instantiated-design-lift, note:pq-we-digit-secret-trapdoor, note:pq-we-quantum-prefix-tree]
tags: [witness-encryption, reduction, sampling, complexity]
---

The internal map H in the design lift is chosen by the reduction. Ordinary LWE requires its challenge matrix U to be uniform. The reduction only needs a surjective H with an efficient conditional sampler for HP=U and a nearly uniform syndrome of iid short columns. H itself may be fixed. Use the standard power-of-two gadget with no random mixing matrix on this internal interface. Honest suffix keys still use the preceding randomized trapdoor; their public distribution matters. For background on gadget sampling see [Micciancio and Peikert](https://eprint.iacr.org/2011/501).

**Map and sampler.** At modulus 2^K let L=2^a and l=ceil(K/a). Take H block diagonal with d0 copies of (1,L,...,L^(l-1)); the tensor dimension is n=d0 l. Each block is surjective. Its integer kernel basis consists of L e_j-e_(j+1) followed by 2^(K-a(l-1)) e_last. The columns have zero syndrome and absolute determinant 2^K, equal to the kernel index. All squared Gram-Schmidt lengths are bounded by V=L²+1. The ordinary radix expansion lifts a target. For a full n-vector, sample each block independently on its specified syndrome. The same l-dimensional basis preparation serves all d0 blocks, yielding O(l³) preparation and O(d0 l²) arithmetic per design column plus n bounded scalar draws, using the previous fraction-free implementation. These are reduction costs.

**Uniform syndromes without random keys.** For squared factor width s²>=V T, T=b+ceil(log2 n)+4, every backward scalar Gaussian has squared width at least T. By the scalar Poisson estimate of the clocked-preimage note each shifted one-dimensional normalizer is its width times a factor in [1-e,1+e], e<=2^-T. The joint unnormalized coset mass lies between (1-e)^n and (1+e)^n times the product of these widths: bound each conditional normalizer in the normalized backward sampling identity and sum the resulting inequalities over the coset. The product of widths is independent of the target. The resulting mass ratio is at most ((1+e)/(1-e))^n, less than 1+2^-b for b>=1. Therefore the syndrome distribution of an iid Gaussian vector is within 2^-b of uniform. The previous bounded scalar precision T-3 gives conditional column distance at most 2^-b. There is no key-distance term in this interface.

Feed the d0 by B_i n ordinary challenge U to this sampler, with M=B_i n. As before send P and Y+WP. The uniform mask makes the new real secret TH+W uniform independently of the design; the uniform endpoint stays uniform. A public or fixed H does not change this algebra. Each endpoint's design error is at most 2M times 2^-b, by the disjoint-fibers identity and the conditional sampler bound. This may be charged once per endpoint per tree level independently of the number of parent secrets. The latter still enters the single-secret LWE hybrid count and runtime. This argument removes a randomized trapdoor *inside* the reduction, without making a uniform-design approximation for the honest public keys.

**Control.** Repeat the previous (10,4,10) search with d0=K², b=2K and the same assumed wrapper-time and hop-loss exponents. The honest outer gadget parameters are unchanged as rules. Search a=1..256 and K=512..3072. First hold the factor-width rule s=n. Then allow s=ceil(sqrt(V T)); use n s² in place of n³ in the shift moment and n s in place of n² in the ideal-prefix residual calculation. Late and child errors retain their previous width n. Integer caps, the modulus exponent and the outer sampler are recomputed each time. The table compares the lowest recorded packed size per encrypted bit in these searches.

| Internal map and width rule | K | Base LWE dimension | Tensor dimension | Packed bits |
| --- | ---: | ---: | ---: | ---: |
| Previous randomized lift, s=n | 1235 | 1525225 | 847645044 | 4.6047e28 |
| Fixed gadget, s=n | 1159 | 1343281 | 77910298 | 3.2703e26 |
| Fixed gadget, width from sampler | 1414 | 1999396 | 23992752 | 4.4849e25 |

The last row uses a=118 and an integer factor width about 1.78e37. Its logarithm enters the modulus and correctness budget. It also changes the factor distribution inside the unproved quantum evasive-LWE premise. Its ordinary LWE challenge uses up to 24,568,578,048 samples per secret. These figures are conditional model comparisons, without a practical parameter set or full timings. The proof does not show that the two rows have identical hardness. The fixed-width-rule comparison isolates the larger part of the gain.

A counting check constrains further compression by this specific method. If the syndrome of an n-vector is within 1/4 of uniform and at least half the vector mass lies in [-A,A]^n, the image of that box must contain at least 2^(K d0)/4 syndromes. Hence n log2(2A+1)>=K d0-2. The width of the short columns and the tensor dimension cannot both be reduced arbitrarily in a statistically close syndrome lift.

The listing checks two-block digit sampling and the masked challenge equation on 240 toy cases, including a partial final digit and a single-digit gadget. Run from the DAG root.

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

def trial(K,a,flexible):
    base=K*K
    prec=2*K
    digits=(K+a-1)//a
    n=base*digits
    V=(1<<(2*a))+1
    smooth=cs(V*(prec+lg(n)+4))
    factor=smooth if flexible else n
    M=1024*n
    if factor<smooth:return None
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
    moment=2*1024*n*m*2**24*24*(n*factor*factor)**3*4*n*n
    f=unit+(lg(moment)+1)//2+sum(max(8,l*lg(1+l),64+lg(192)+g+l)
                                 for l,g in zip(L,gains))
    def z(N):return cs((68+lg(6*N)+3)//4)
    A=z(C*m)*sigma
    scalar=z(2064*(n*n+r*m+n*m))
    residual=scalar<<f
    for i in (1,2):
        residual=m*A*residual+24*(n*factor*scalar)**i*scalar*n
    if 16*(residual+1)>1<<K:return None
    bits=min(K,lg(2*A+1))
    return (1024*K*m+bits*m*C,K,a,digits,base,n,M,factor,m,sigma,bits)


def main():
    for flexible in (False,True):
        rows=[]
        for a in range(1,257):
            for K in range(512,3073):
                out=trial(K,a,flexible)
                if out is not None:
                    rows.append(out)
                    break
        print(flexible,len(rows),min(rows))
main()

def controls():
    from random import Random
    ns={}
    for slug in ('clocked-preimage','ordered-radix-gadget','fraction-free-preimages'):
        src=Path('dag/Notes/pq-we-'+slug+'.md').read_text()
        exec(src.split('~~~python\n',1)[1].split('\n~~~',1)[0],ns)
    rng=Random(491)
    draw=ns['filtered_sampler'](ns['sample_squared'],ns['threshold'])
    checks=0
    for K,a in ((4,1),(5,2),(7,3),(6,6)):
        q=1<<K
        l=(K+a-1)//a
        L=1<<a
        cols=[]
        for j in range(l):
            v=[0]*l
            if j+1<l:v[j],v[j+1]=L,-1
            else:v[j]=1<<(K-a*j)
            cols.append(v)
        dirs=ns['gram_prepare'](cols)
        assert all(det<=((1<<(2*a))+1)*prev for _,prev,det in dirs)
        n=2*l
        T=10+lg(n)+4
        sig=cs((L*L+1)*T)
        for y in range(q):
            U=[y,rng.randrange(q)]
            P=[]
            for u in U:
                lift=[(u>>(j*a))%(1<<a) for j in range(l)]
                x=ns['gram_draw'](cols,dirs,lift,sig*sig,T-3,rng.getrandbits,draw)
                assert sum(v<<(j*a) for j,v in enumerate(x))%q==u
                P+=x
            secret=[rng.randrange(q) for _ in U]
            W=[rng.randrange(q) for _ in P]
            E=rng.randrange(5)-2
            lhs=sum(x*y for x,y in zip(secret,U))+E+sum(x*y for x,y in zip(W,P))
            rhs=sum((W[j]+(secret[j//l]<<(a*(j%l))))*x for j,x in enumerate(P))+E
            assert (lhs-rhs)%q==0
            checks+=1
    print("two-block tests",checks)
controls()
~~~
