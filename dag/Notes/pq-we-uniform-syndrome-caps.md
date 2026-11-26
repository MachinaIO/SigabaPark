---
title: Uniform syndrome masses and simultaneous signed caps for dyadic WE preimages
refs: [definition:WE_CircuitSAT, note:pq-we-priced-endpoints, note:pq-we-quantum-preimage-hop]
tags: [witness-encryption, correctness, sampling, complexity]
---

The last projected layout assumed a cap on sampled preimage coefficients. For a uniform public key at the actual dyadic dimensions, the following bound works simultaneously for *all* target syndromes. It avoids a factor q^r in the individual tail probability. It applies to ideal conditional Gaussians and transfers with explicit additive key and sampler distances.

**Public key estimate.** Let q=2^K, A uniform of shape r by m over Z/q, and X have independent zero-centered discrete Gaussian coordinates of width s, with mass proportional to exp(-pi x²/s²). Define Delta(A)=max_y |q^r Pr[AX=y | A]-1|. The characteristic function phi of one coordinate is real and nonnegative by Poisson summation, including at each modular frequency. Fourier inversion and the triangle inequality bound Delta by the sum of the nontrivial Fourier coefficients; equality holds at syndrome zero. For h of additive order 2^j, its dot product with a uniform column has that order's full cyclic subgroup as its uniform range. Averaging phi over the subgroup gives Pr[2^j divides X_1]. Columns are independent, so E Delta is exactly the sum over nonzero h of this divisibility probability to the mth power. The scalar normalizer is at least s by Poisson summation. Integral comparison on the decreasing positive half-line bounds the unnormalized mass on multiples of d by 1+s/d. Hence the divisibility probability is at most 1/d+1/s. These are elementary applications of [Gaussian Fourier analysis on lattices](https://cims.nyu.edu/~regev/papers/average.pdf).

At s>=8 the at most 2^r order-two characters contribute at most 2^r(5/8)^m; all others together contribute at most q^r(3/8)^m. For m>=2rK and K>=2 this gives E Delta <= 2^(1-r(K-1)), since (5/8)^2<=1/2 and 3/8<=1/2. Markov implies Pr[Delta>1/2] <= 2^(2-r(K-1)). On a good key every syndrome has positive mass, and the ratio of any two masses is at most three. For a key whose public marginal is delta_key away from uniform add delta_key to its bad-key bound; union bound over keys. No independence across target syndromes is required.

**Conditioned coordinate.** Take integer width s and integer z>=1. On x_i>=zs, translating x to x-zs e_i changes its syndrome by a fixed offset and gives weight(x) <= exp(-pi z²) weight(x-zs e_i). Divide the two syndrome masses on a good key and use their ratio. The negative tail obeys the same bound. Consequently Pr[|X_i|>=zs | AX=y] <= 6 exp(-pi z²) <= 6 times 2^(-4z²) for every y. This is uniform in adaptive choices of y when the fresh draw given key and history is the designated conditional law. For E transmitted preimage coordinates take the smallest integer z with 6 E 2^(-4z²) <= 2^(-lambda-4). Union bounding costs no assumption that coordinates of a preimage column are independent. For an unconditional centered integer-width scalar Gaussian the syndrome ratio is one. Its parity imbalance is at most 1/s: the alternating weighted sum has absolute value at most one by the alternating-series estimate and the normalizer is at least s. Thus s>=2 satisfies the parity atom cap 3/4 used for tensor-row survival. Differentiating the Poisson normalizer gives variance at most s²/(2pi).

**Control and remaining premises.** Reuse the prior (10,4,10) program, K=1036, n=1,073,296, r=24n, m=53,372,863,488 and 34 final columns. For width s=326,720 the 853,965,850,624 retained columns require z=7 for the 2^-68 coordinate-overflow budget. This permits a signed slot of 23 bits. A separate conservative count of tensor and additive scalar entries gives z=6 for its own 2^-68 budget. Both fit inside the earlier residual calculation with z=110; keep that larger residual certificate unchanged. With the same root residue encoding the new total is 1,048,307,920,303,026,138,513,408 bits versus 1,230,622,331,378,100,344,979,456. This comparison changes the wire encoding only. For the projected decoder only transmitted preimage coordinates enter evaluation; bounding all full scalar matrices is conservative. Correctness loss must also include bad keys, root survival, terminal-key distance, terminal shortness, and the sum of actual conditional sampling errors. Uniform public syndromes do not supply a trapdoor algorithm that samples at this width. In particular a trapdoor with Gaussian width requirements above s would require repricing. Quantum evasive-LWE hiding remains open.

The listing uses exact integer threshold checks for the WE dimensions. As a separate numerical check it enumerates all public matrices at q=4,8 and compares the mean maximum syndrome deviation against the character formula with a scalar Gaussian truncated at twelve widths. These are arithmetic controls rather than tests at cryptographic dimensions.

~~~python
from math import isqrt, exp, pi
from pathlib import Path
from itertools import product

def sqrt_up(x):return isqrt(x-1)+1
def lg(x):return (x-1).bit_length()

def cap_factor(entries,lam):
    return sqrt_up((lam+4+lg(6*entries)+3)//4)

def account():
    s=Path('dag/Notes/pq-we-stage-gap-search.md').read_text()
    env={'__name__':'planner'}
    exec(s.split('~~~python\n',1)[1].split('\n~~~',1)[0],env)
    B=[1024,16,1024]
    (K,n,_,_),_=env['solve'](B,24,64,2,'budget')
    r=24*n
    m=2*r*K
    t=34
    columns=B[1]*m+B[2]*t
    entries=columns*m
    scalars=sum(B)*(n*n+r*m+n*m)
    z=cap_factor(entries,64)
    zs=cap_factor(scalars,64)
    width=2*(isqrt(r*K)+1)
    old_z=64+lg(3*m)+8
    old_b=(2*old_z*width).bit_length()
    new_b=(2*z*width).bit_length()
    assert max(z,zs)<=old_z
    assert 6*entries*2**68<=1<<(4*z*z)
    assert 2*scalars*2**68<=1<<(4*zs*zs)
    print(K,n,m,columns,z,zs,width,old_z,old_b,new_b)
    print("payload",B[0]*K*m+entries*old_b,B[0]*K*m+entries*new_b)

def check(q,m,s):
    # Numerical illustration only: truncate the scalar Gaussian at 12 widths.
    masses=[0.0]*q
    for x in range(-12*s,12*s+1):
        masses[x%q]+=exp(-pi*(x/s)**2)
    total=sum(masses)
    masses=[x/total for x in masses]
    empirical=0.0
    for A in product(range(q),repeat=m):
        law=[1.0]+[0.0]*(q-1)
        for a in A:
            dest=[0.0]*q
            for y in range(q):
                for x in range(q):
                    dest[(y+a*x)%q]+=law[y]*masses[x]
            law=dest
        dev=max(abs(q*p-1) for p in law)
        assert abs(dev-(q*law[0]-1))<1e-11
        empirical+=dev/q**m
    predicted=sum((sum(masses[::1<<d]))**m*(1<<(d-1))
                  for d in range(1,q.bit_length()))
    assert abs(empirical-predicted)<1e-10
    print(q,m,s,empirical,predicted)
account()
check(4,4,2)
check(8,4,3)
~~~
