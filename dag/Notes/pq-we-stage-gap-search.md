---
title: Least feasible modulus exponent and stage-specific noise separation
refs: [definition:WE_CircuitSAT, note:pq-we-joint-dyadic-envelope, note:pq-we-root-loss-budget]
tags: [witness-encryption, complexity, reduction]
---

In the joint dyadic envelope the modulus q=2^K is a power of two for every positive integer K. Requiring K itself to be a power of two discards feasible parameters even when the noise-separation policy is fixed. A second, distinct choice is the logarithmic gap between consecutive PRE error widths. [VWW, Definition 3.1 and Remark 5.1](https://ntt-research.com/wp-content/uploads/2023/01/Witness-encryption-and-null-iO-from-evasive-LWE.pdf) discuss a much smaller second PRE error width and quantitative hardness scaling. Merely showing that a new gap is superpolynomial does not transfer an assumption proved or postulated only at the old widths. We price that choice independently.

**Exact search.** Keep the preceding planning model with n=K^a, hop exponent one, simulation exponent two and all common width, moment, correctness and time bounds. Given K compute the required lower bound R(K) from the largest of the time exponent, advantage exponent, the integer a-th root needed for tensor survival, and the ceiling of log2(16(B+1)) for the residual B. In these formulas every right-hand quantity is nondecreasing in K, including all prefix scales and the preimage support bound. At an infeasible K, every integer from K through R(K)-1 is infeasible, since its requirement is at least R(K). Starting at one and replacing K by R(K) therefore finds the least feasible exponent. Termination follows from the polynomial-in-log-K upper bounds for fixed program and security inputs; for increasing inputs the previous polynomial envelope bounds the number of increments. This proof is valid without assuming that feasibility itself is monotone. The result is a minimum within the stated sufficient inequalities.

**Alternative gap profile.** Write L_i=ceil(log2(S P_i)) and G_i=sum_(j<=i) L_j for the cumulative multiplier exponent. The old log gap is max(8,L_i²). The trial policy takes the largest of 8, L_i ceil(log2(1+L_i)), and lambda+ceil(log2(64H))+G_i+L_i. The middle term still gives a width ratio exceeding every fixed power of S P_i asymptotically. The last term separately budgets a hypothetical local loss at most (S P_i) divided by the width ratio: even after multiplication by 2^G_i it contributes at most 2^-lambda/(64H). This is an explicit tolerance calculation, not a derivation of such a loss law for evasive LWE. All earlier additive errors still need their own certificates. Hardness at the revised widths, time and gain envelopes, and sampler accuracy remain assumptions. The alternative need not give a smaller gap on every input.

**Fixed-shape comparison.** The same 2^24-path controls use w=24, lambda=64 and a=2. Columns give the modulus exponent K; n=K² in every cell.

| Levels and arity | Old grid and square gap | Least K at same square gap | Least K at alternative gaps |
| --- | ---: | ---: | ---: |
| 24 binary | 131072 | 112422 | 24013 |
| 12 four-way | 65536 | 49314 | 7267 |
| 8 eight-way | 32768 | 29583 | 3845 |

For the eight-way control, refining the grid alone lowers the modeled raw payload from 5.234e36 to 2.558e36 bits. Changing the gap profile as well yields 1.603e30 bits and n=14,784,025. No row is close to a practical encryption, and no concrete quantum security level is certified. In particular the gain from the last column depends on the evasive-LWE interface at a different width ratio. The listing computes the residual exactly without constructing q-sized arrays. Each of the six large cases reached its least exponent in six or seven evaluations and 18 smaller cases agree with exhaustive integer search.

~~~python
from math import isqrt
from itertools import accumulate
from operator import mul

def lg(x):
    return (x-1).bit_length()

def root(x,a):
    lo,hi=0,x
    while hi-lo>1:
        mid=(hi+lo)//2
        if mid**a>=x:hi=mid
        else:lo=mid
    return hi

def requirement(K,B,w,lam,a,policy):
    H=len(B)
    n=K**a
    m=2*n*w*K
    S=2+lam+H+w+n+m+K+max(B)
    P=list(accumulate(B,mul))
    L=[lg(S*p) for p in P[:-1]]
    gains=list(accumulate(L))
    G=sum(L)
    hbits=lg(64*H)
    unit=lam+hbits+G
    time=G+lg(H+2)+max(lam,2*lg(S*P[-1]))
    hardness=unit+lg(w*m*H*P[-1])
    M=2*max(B)*n*m*P[-1]*w*(n**3)**H*(H+1)*n*n
    terminal=unit+(lg(M)+1)//2
    if policy=='square':
        gaps=[max(8,l*l) for l in L]
    else:
        gaps=[max(8,l*lg(1+l),lam+hbits+g+l) for l,g in zip(L,gains)]
    f=terminal+sum(gaps)
    z=lam+lg(H*m)+8
    col=m*z*2*(isqrt(n*w*K)+1)
    residual=z<<f
    for i in range(1,H):
        residual=col*residual+w*(n*z*n)**i*z*n
    needed=max(time,hardness,root(lam+lg(H)+6,a),lg(16*(residual+1)))
    payload=K*(B[0]*n*m+sum(B[1:])*m*m)
    return needed,(K,n,f,payload)

def solve(B,w,lam,a,policy):
    K=1
    steps=0
    while True:
        need,data=requirement(K,B,w,lam,a,policy)
        steps+=1
        if need<=K:
            assert K==1 or requirement(K-1,B,w,lam,a,policy)[0]>K-1
            return data,steps
        K=need

if __name__=='__main__':
    for policy in ('square','budget'):
        for H,b in ((24,2),(12,4),(8,8)):
            print(policy,H,solve([b]*H,24,64,2,policy))
        for a in (1,2,3):
            for B in ([2],[2,3],[3,1,4]):
                result,_=solve(B,2,8,a,policy)
                brute=next(k for k in range(1,result[0]+1)
                           if requirement(k,B,2,8,a,policy)[0]<=k)
                assert brute==result[0]
~~~
