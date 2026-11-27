---
title: Integer rank survival and terminal decoding with nonunit tensor coefficients
refs: [definition:WE_CircuitSAT, note:pq-we-tensor-rank-survival, note:pq-we-ordered-radix-gadget, note:pq-we-packed-columns]
tags: [witness-encryption, correctness, complexity]
---

The earlier correctness test discarded a witness path as soon as its tensor product vanished modulo the prime p underlying q=p^j. A nonzero integer coefficient divisible by p can still deliver an easily detected signal modulo q. This permits a trade between tensor dimension n and scalar Gaussian width s. It is a property of honest decoding, independent of whether the resulting parameters support the security proof. In particular, scalar tensor factors are a correctness control and provide no evidence of post-quantum message hiding.

**Integer survival.** For a fixed valid witness, retain d root rows and multiply the corresponding standard rows by H independent integer tensor factors. Bound the probability of rank zero over the rationals using the same rank-transition recursion as in the preceding note. The pivot argument works over the rationals: after conditioning on the nonpivot coordinates, each remaining integer is forced to at most one value. The parameter rho now bounds single integer atoms, without folding the distribution modulo p. For center-zero Gaussian entries with weight exp(-pi x²/s²), Poisson summation gives a normalizer s times the sum of exp(-pi s²k²) over integer k, at least s. Thus the maximum ideal atom is at most 1/s. With bounded scalar precision b_s the implemented maximum is at most rho=1/s+2^(-b_s). Independent coins are essential. A power-of-two s=2^e has an (e+1)-bit representation, and the bounded scalar sampler runs in polynomial bit time in e and b_s even for large numerical widths. For integer s its shell support at center zero gives the absolute entry cap S=t_s s including the fallback.

**Terminal law.** Each entry of the product of H tensor factors has absolute value at most M=(nS)^H. On survival choose a nonzero entry u using only the tensor factors and witness. In its output row the terminal ideal coefficient vector v contains u times a unit logical coordinate on a valid message-one path. For a uniform terminal column Z, vZ modulo q is exactly uniform on the multiples of g=gcd(v_1,...,v_N,q), because the image of the additive homomorphism has constant fiber size. The unit coordinate implies g divides u and g<=M. In an interval of 4B+1 consecutive integers there are at most (4B+1)/g+1 such multiples. Therefore one column lands in the ideal interval with probability at most (4B+1+M)/q. Here B is the recomputed evaluation residual cap, and q>=16(B+1+M) rules out wrap ambiguity and forces M<q. A decoder declaring zero only when every retained entry is short fails on one with probability at most the integer extinction bound plus ((4B+1+M)/q)^t plus the terminal public-matrix distance. The t uniform columns in this argument are independent conditional on the chosen ideal row. Correlated residuals cannot increase the event beyond this expanded interval. Zero still decrypts deterministically on a valid path. The modulus selection reruns the earlier fixed-radix search with the stronger monotone lower bound. Its bit length remains polynomial because log M=H log(nS). For example, at n=1 the extinction probability is at most H rho, so choosing e and b_s linear in the failure-bit target and logarithmic in H suffices. This gives an honest correctness family, with no cryptographic dimension floor imposed.

**Accounting control.** Fix H=8, w=6, p=7, lambda=32 and E=16. Recompute S, the residual, q, all matrix dimensions, packing, row count and terminal column count for every candidate. The previous width-two reference had 58407566376 packed bits per message bit. Searching n=1,...,5, e=1,...,39 and radix exponents 1,...,16, the smallest payload in this grid is 1284644942 bits. It uses n=1, s=2^36, b_s=40, q=7^110, radix 64, m=2260, one root row and seven terminal columns. It calls the preimage-column sampler 27134 times and uses 30661420 multiply-adds across the seven decryption matrix products. At n=2 the best control in the same grid has 2298945768 bits at e=18. These calculations include the larger factor entries in noise growth and the nonunit penalty in the final test. They do not time the sampler or account for a security reduction. Increasing the tensor width changes the actual public ciphertext law; the previous width's security premises cannot be transferred by the correctness analysis.

**Checks.** For seven small prime powers, enumerating all uniform columns against two-dimensional coefficient rows verified the exact subgroup law and the terminal interval inequality in 2960 row-and-threshold cases, including 248 with nonunit gcd. In 100 fixed-seed executions of the clocked width-2^36 scalar sampler along eight-factor paths, 75 products were nonunits modulo 7^110. Every product was nonzero and below the public magnitude cap. This test illustrates why the integer analysis matters; the analytic bounds certify the target probability.

The planner uses account from the ordered-radix note, layout from the packing note, and rank_rows from the full-root survival note. Its search assumes H>=2, n,w,lambda,E>=1, e>=1, and an admissible public prime p. The result fields are as in the earlier rank planner.

~~~python
from fractions import Fraction as F
from math import isqrt

def integer_plan(H,w,n,p,lam,e,E,account,layout,rank_rows):
    """Width 2^e, binary precision at least e+4; full intermediate blocks."""
    width=1<<e
    bs=max(e+4,lam+(2*H*n*n-1).bit_length()+4)
    S=(isqrt((bs+12)//4)+1)*width
    magnitude=(n*S)**H
    rho=F(1,width)+F(1,1<<bs)
    rows=rank_rows(n,rho)
    bad=[F(1)]+[F(0)]*n
    for _ in range(H):
        bad=[sum(x*y for x,y in zip(row,bad)) for row in rows]
    key_bits=lam+(H-1).bit_length()+3
    slack=[F(1,1<<lam)-v-F(1,1<<key_bits) for v in bad]
    if slack[-1]<=0:
        return None
    best=None
    for a in range(1,17):
        j=1
        while True:
            q=p**j
            c=account(H,w,n,q,lam,S,E,a)
            needed=16*(c['B']+1+magnitude)
            if q>=needed:
                break
            lo,hi=j,needed.bit_length()
            while hi-lo>1:
                mid=(hi+lo)//2
                if p**mid>=needed:
                    hi=mid
                else:
                    lo=mid
            j=hi
        m=c['m'];cap=layout(m,q,c['C'])[0]
        box=F(4*c['B']+1+magnitude,q)
        for d in range(1,n+1):
            if slack[d]<=0:
                continue
            t=1
            while t<=m and box**t>=slack[d]:
                t+=1
            if t<=m:
                cols=2*((H-2)*m+t)
                cost=(2*d*m*c['k']+cols*cap,a,j,m,d,t,cols,d*((H-2)*m*m+m*t))
                if best is None or cost<best:
                    best=cost
    return best
~~~
