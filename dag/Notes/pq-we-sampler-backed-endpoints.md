---
title: Repricing projected WE endpoints with a clocked gadget trapdoor
refs: [definition:WE_CircuitSAT, note:pq-we-uniform-syndrome-caps, note:pq-we-priced-endpoints, note:pq-we-clocked-preimage, note:pq-we-ordered-radix-gadget, note:pq-we-fraction-free-preimages]
tags: [witness-encryption, sampling, correctness, complexity]
---

The previous 23-bit account priced an ideal preimage Gaussian of width 326,720. Its syndrome estimate does not provide an algorithm for drawing that Gaussian. Here we instantiate the existing bounded carry-first sampler, use its certified width, recompute its column caps and recheck the actual residual.

**Honest setup and draws.** For rank r, modulus 2^K and radix 2^a let ell=r ceil(K/a), h=rK+2(b_key+ceil(log2 ell)), m=h+ell. Use the binary secret R and public [U | G-UR] key from the ordered gadget note, based on [Micciancio and Peikert](https://eprint.iacr.org/2011/501). Uniform U is exact at the dyadic modulus. For each fixed key the carry-first basis has all squared Gram-Schmidt lengths at most V=2^(2a)(h+1)+1. With C retained preimage columns take b_key=lambda+ceil(log2 H)+4, b_pre=lambda+ceil(log2 C)+4 and T=b_pre+ceil(log2 m)+4. Choose integer sigma=ceil(sqrt(V T)). The backward sampler's normalized squared scalar widths are at least T. The earlier Poisson and scalar-clock estimates then give conditional distance at most 2^-b_pre from the ideal coset law for each key, basis and target, with exact syndrome even on scalar timeout. Its scalar precision is T-3. The joint public-key marginal is within H times 2^-b_key of uniform independent keys when generated separately. Fresh coins and sequential replacement bound the complete retained-column sampling distance by C times 2^-b_pre. Each of these two budgets is at most 2^(-lambda-4). Omitted columns are not needed to form later encryption targets; the independent-column law gives the same marginal by skipping them. For an ideal full-ciphertext hiding argument these two endpoint changes must be charged, as must any sampling done internally by its reductions at their induced budgets.

**Shorter keys.** The old syndrome estimate assumed m>=2rK, while this sampler only guarantees m>=rK. Reuse the preceding character calculation: for sigma>=8, E Delta <= 2^r (5/8)^m + 2^(rK) (3/8)^m <= 2^(r-m/2)+2^(rK-4m/3). Both exponents are strongly negative in these examples. Twice this bound covers the probability of an ideal key on which a syndrome-mass ratio might exceed three. Key distance is accounted for once. The uniform conditional tail then allows A_cap=z sigma with 6 m C exp(-pi z²) <= 2^(-lambda-4). The packed width is ceil(log2(2 A_cap+1)) or K if smaller. Recompute the actual path residual with column norm bound m A_cap. Keep the previous conservative root flooding width calculated at m_old=2rK and require m<=m_old; charge the actual tensor and error caps. Extra statistical errors of any nonideal scalar draws for factors, root and late errors must be budgeted separately.

**Control.** The input is the (10,4,10) layout at logical width 24, lambda=64 and n=K². At fixed K=1036, radix 16 gives m=33,358,039,886 and certified sigma=31,582,149. It takes 29 bits per retained entry and costs 5.1632e23 bits. The earlier ideal-width 23-bit account at the same K used m=53,372,863,488 and cost 1.0483e24 bits. Thus the shorter gadget key more than offsets the wider coefficient. Among radix exponents 2 through 16, allowing K to increase, the minimum is a=6,K=1039, m=31,427,015,558, sigma=126,877,715 and 31 bits per entry. The retained column count is 502,832,283,744 and the raw packed total is 4.8988e23 bits per message bit. For each radix the listing checks every exponent from the previous full-envelope lower bound 1036 through its first feasible value. The price is nondecreasing with K at fixed radix. A different proof envelope, basis, radix range or modulus choice can change the minimum.

These are costs for an explicitly clocked honest preimage algorithm, not measured full encryptions. The excellent syndrome probabilities alone did not certify the previous smaller sigma, and the present bound does not prove that smaller widths are impossible. Basis preparation and draws have polynomial bit complexity by the fraction-free sampler analysis; basis dimension in the tens of billions prevents a practical execution of the reported controls. Quantum hiding of the root and the transition hops at the new m and sigma still requires the corresponding hardness premises. Neither hardness at the old width nor a claim about security at a common concrete level follows from the honest sampler calculation.

The small control invokes the actual carry-first key generator and fraction-free Gaussian sampler at three dyadic moduli and checks every target syndrome, 56 generated columns total. Run from the DAG root.

~~~python
from math import isqrt
from pathlib import Path
from random import Random

def listing(slug,idx=1):
    return Path('dag/Notes/pq-we-'+slug+'.md').read_text().split('~~~python\n')[idx].split('\n~~~')[0]

def sqrt_up(x):return isqrt(x-1)+1
def lg(x):return (x-1).bit_length()
def cap(N,lam):return sqrt_up((lam+4+lg(6*N)+3)//4)

def price(K,a):
    ns={'__name__':'planner'}
    exec(listing('stage-gap-search'),ns)
    B=[1024,16,1024]
    required,(_,n,f,_)=ns['requirement'](K,B,24,64,2,'budget')
    if K<required:return None
    r=24*n
    ell=r*((K+a-1)//a)
    keybits=64+lg(len(B))+4
    h=r*K+2*(keybits+lg(ell))
    m=h+ell
    if m>2*r*K:return None
    columns=B[1]*m+B[-1]*34
    prebits=64+lg(columns)+4
    T=prebits+lg(m)+4
    sigma=sqrt_up(((1<<(2*a))*(h+1)+1)*T)
    A=cap(m*columns,64)*sigma
    z=cap(sum(B)*(n*n+r*m+n*m),64)
    residual=z<<f
    for i in range(1,len(B)):
        residual=m*A*residual+24*(n*z*n)**i*z*n
    if 16*(residual+1)>1<<K:return None
    # m>=rK permits the relaxed uniform-syndrome bound in this note.
    assert m>=r*K and r*(K//2-1)>=70 and r*K//3>=70
    bits=min(K,lg(2*A+1))
    return (B[0]*K*m+bits*m*columns,K,a,m,sigma,bits,columns)

def search():
    # K starts at the previous common-envelope lower bound. For each radix
    # the payload is nondecreasing with K, even if feasibility has jumps.
    rows=[]
    for a in range(2,17):
        for K in range(1036,1101):
            record=price(K,a)
            if record is not None:
                rows.append(record)
                break
    print("fixed K",min(x for a in range(2,17) if (x:=price(1036,a)) is not None))
    assert len(rows)==15
    print("best",min(rows),"radix four",rows[0])

def control():
    ns={}
    for slug in ('clocked-preimage','ordered-radix-gadget','fraction-free-preimages'):
        exec(listing(slug),ns)
    rng=Random(731)
    draw=ns['filtered_sampler'](ns['sample_squared'],ns['threshold'])
    count=0
    for q,a in ((8,2),(16,2),(32,3)):
        mat,basis,lift=ns['radix_setup'](1,q,4,a,rng.getrandbits)
        m=len(basis)
        ell=((q-1).bit_length()+a-1)//a
        T=8+lg(m)+4
        width=sqrt_up(ns['radix_quality'](m-ell,a)*T)
        dirs=ns['gram_prepare'](basis)
        for y in range(q):
            x=ns['gram_draw'](basis,dirs,lift([y]),width**2,T-3,rng.getrandbits,draw)
            assert sum(v*u for v,u in zip(mat[0],x))%q==y
            count+=1
    print("sampled syndromes",count)
search()
control()
~~~
