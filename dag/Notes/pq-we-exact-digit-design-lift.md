---
title: Exact ordinary-LWE design lifting with centered randomized digits
refs: [definition:WE_CircuitSAT, note:pq-we-fixed-gadget-design-lift, note:pq-we-quantum-prefix-tree]
tags: [witness-encryption, reduction, sampling, complexity]
---

Change the honest iid tensor-factor entries to a bounded centered digit law. This permits an exact map from a uniform public matrix in the ordinary-LWE challenge to the short-design matrix of the isolated prefix tree. No Gaussian preimage sampling, approximating the marginal, or trapdoor setup is needed at *this* interface. The honest ciphertext's suffix preimages still use the outer Gaussian trapdoor. The underlying radix gadget is of the type used in [Micciancio and Peikert](https://eprint.iacr.org/2011/501).

**Digits conditional on a syndrome.** Write q=2^K, L=2^a and l=ceil(K/a). Given a uniform challenge entry u, append al-K independent high bits to obtain v uniform modulo L^l. At each step take c=v mod L. Return digit x=c for c<L/2 and x=c-L for c>L/2. At c=L/2 return either sign of L/2 with an independent fair bit. Replace v by (v-x)/L and continue l times, finally discarding the remaining carry. For every choice of coins, the radix evaluation of these digits equals u modulo q. Given c and its tie coin, the quotient modulo the next radix power is a uniform upper part translated by a fixed carry. Induction gives independent digits, across positions as well as across challenge entries. Their common law assigns mass 1/L to every integer strictly between -L/2 and L/2, and 1/(2L) to each endpoint. The mean is zero, variance (L²+2)/12, and parity is exactly uniform. This proof also covers a partial final digit and a=1. For a fixed u, the output law is exactly the conditional law of these iid digits given their radix syndrome: the unconditional product law and exact syndrome identity determine the disintegration.

**Tree switch.** Use d0 independent syndrome coordinates with block gadget H, tensor dimension n=d0 l, and M=B_i n columns of the ordinary public challenge U. Lift each coordinate separately to obtain P with HP=U. In the real case Y=T U+E, the pair (P,Y+WP) has the honest short-design law since TH+W is uniform independent of the iid digit design and the errors. In the uniform case the masked response is independent uniform given P. Both endpoint distribution errors from the design lift are zero. The single-secret ordinary quantum LWE hybrids, label sample counts, noisy-tree flooding and the separate root evasive-LWE implication still enter. Each lift takes O(l) radix operations per syndrome coordinate and requires no all-column smoothing allowance. Honest tensor generation directly samples residues and tie coins. No change to branch labels or witness processing is required.

**Repricing.** Use the preceding (10,4,10) example, d0=K², outer trapdoor exponents six, and the same supplied time and loss envelopes. In the tree moment use n ceil((L²+2)/12) in place of the Gaussian second-moment multiplier. In the correctness recurrence the absolute tensor cap is exactly L/2. Tensor extinction for the single retained row has per-level upper bound 2^-n. Retain the separate late-error and projected-preimage budgets. All arithmetic is polynomial for polynomial bit lengths and polynomial input dimensions. Enumerate radix exponents 1..256 and record the first passing K in 512..3072 for each. All 256 yield a feasible point. The smallest packed size among these records uses K=1385, a=116, l=12, d0=1,918,225 and n=23,018,700. The largest ordinary challenge has 23,571,148,800 samples per secret. The packed cost is 3.9578e25 bits per encrypted bit, versus 4.4849e25 for the preceding Gaussian gadget's flexible-width search. With a capped at twenty the least recorded payload is 2.7861e26 bits, at K=1135 and n=73,428,825. These are numerical model comparisons, not measurements or a common concrete security guarantee. The largest digit in the first choice has magnitude 2^115. In particular the root sampler's factor distribution changed: quantum evasive-LWE for that family is still an assumption, and is not implied by the corresponding Gaussian-family hypothesis.

The executable control enumerates the complete output laws at seven tiny modulus/radix choices. It verifies the syndrome equation for 1,940 input and coin patterns and checks every joint digit probability against the claimed product law.

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

def trial(K,a):
    base=K*K
    digits=(K+a-1)//a
    n=base*digits
    radix=1<<a
    factor=radix//2
    variance=(radix**2+2+11)//12
    M=1024*n
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
    moment=2*1024*n*m*2**24*24*(n*variance)**3*4*n*n
    f=unit+(lg(moment)+1)//2+sum(max(8,l*lg(1+l),64+lg(192)+g+l)
                                 for l,g in zip(L,gains))
    def z(N):return cs((68+lg(6*N)+3)//4)
    A=z(C*m)*sigma
    scalar=z(2064*(n*n+r*m+n*m))
    residual=scalar<<f
    for i in (1,2):
        residual=m*A*residual+24*(n*factor)**i*scalar*n
    if 16*(residual+1)>1<<K:return None
    bits=min(K,lg(2*A+1))
    return (1024*K*m+bits*m*C,K,a,digits,base,n,M,factor,m,sigma,bits)



def scan():
    rows=[]
    for a in range(1,257):
        for K in range(512,3073):
            row=trial(K,a)
            if row is not None:
                rows.append(row)
                break
    print("searched",len(rows),"best",min(rows))
    print("a <= 20",min(row for row in rows if row[2]<=20))
scan()

from collections import Counter
from fractions import Fraction as F
from itertools import product

def lift(u,K,a,padding,ties):
    radix=1<<a
    value=u+(padding<<K)
    out=[]
    for tie in ties:
        digit=value%radix
        if digit>radix//2 or (digit==radix//2 and tie):
            digit-=radix
        out.append(digit)
        value=(value-digit)//radix
    return tuple(out)

def check():
    cases=0
    for K,a in ((1,1),(2,3),(3,1),(4,2),(5,2),(5,3),(6,4)):
        l=(K+a-1)//a
        radix=1<<a
        hist=Counter()
        for u,p,ties in product(range(1<<K),range(1<<(a*l-K)),product(range(2),repeat=l)):
            v=lift(u,K,a,p,ties)
            assert sum(x<<(j*a) for j,x in enumerate(v))%(1<<K)==u
            hist[v]+=1
            cases+=1
        weights={v:F(1 if abs(v)==radix//2 else 2,2*radix)
                 for v in range(-radix//2,radix//2+1)}
        assert sum(p*v for v,p in weights.items())==0
        assert sum(p*v*v for v,p in weights.items())==F(radix**2+2,12)
        assert sum(p for v,p in weights.items() if v%2)==F(1,2)
        for v in product(weights,repeat=l):
            expected=F(1)
            for x in v:expected*=weights[x]
            assert F(hist[v],sum(hist.values()))==expected
    print("joint-law trials",cases)
check()
~~~
