---
title: Stage-weighted flooding for exact digit designs
refs: [note:pq-we-exact-digit-design-lift, note:pq-we-root-loss-budget, note:pq-we-priced-endpoints]
tags: [witness-encryption, complexity, correctness, reduction]
---

In the digit construction, replacing the uniform worst-case flooding estimate by the stage schedule reduces the tensor and key dimensions needed by the numerical control. The honest correctness recurrence already stops before the final tensor amplification. The change here is to the statistical part of the security reduction.

For arities B_j let P_j be their prefix product, w the Boolean logical width, and U_j <= w P_j the sum of squared logical row norms. Let n be the tensor dimension, m the column count, v an upper bound on the centered entry variance, and e=n² an upper bound for the two fresh error variances in this control. By the prefix-tree moment calculation, the isolated table at level j has shift second moment at most n m U_j e times the sum of (nv)^k for 0 <= k < j. The extra PRE shift into level j+1 has moment at most n m U_j e B_(j+1) (nv)^j by summing squared entries over the next labels. In particular the variance of the last tensor factor never multiplies an injected error in either expression. Public factor generation, computational hybrids and honest survival still use the full family.

For each shift of moment at most M charge ceil(sqrt(2M)) divided by its flooding width, multiplied by the cumulative reduction loss through j (through H-1 for the terminal isolated table). Use the old minimum adjacent gaps at equality. If d is the cumulative gap exponent before the receiving level, its width is the root width divided by 2^d. Sum the rounded weighted coefficients times 2^d, obtaining N. A dyadic root width with exponent max(total gap exponent,68+ceil(log2 N)) suffices for flooding loss 2^-68 per message and integral downstream widths. This only prices the flooding terms. Quantum evasive LWE must hold for the actual new widths, losses and running times, and the underlying LWE and preimage assumptions must cover the selected parameters.

The scan fixes the previous three blocks (10,4,10), logical width 24, and the remaining gap, time, hybrid and correctness checks. It records the first passing modulus exponent K in 512..3072 for each digit exponent a in 1..256. All 256 pass somewhere. The smallest recorded payload has K=1352, a=169, tensor dimension 14,623,232 and key width m=158,398,849,060. The prior comparison has K=1385 and a=116. Payload falls from 3.95784e25 to 1.52548e25 bits per plaintext bit. Encryption draws 2,534,381,619,776 suffix preimage columns versus 4,082,228,368,192. Dense decryption uses 2.50902e22 modular multiply-adds versus 6.50960e22. These are projected-format resource counts. Column counts exclude setup, target formation, and the cost per sample. The restricted scan a<=20 gives 1.83943e26 payload bits at K=1079. No cryptographic execution or concrete security level is certified.

For a growing input, polynomial honest cost requires polynomial logical program size, a polynomial-size public table alphabet (e.g. blocks of O(log input size) bits), polynomial dimensions and modulus bit length, and polynomial-time bounded samplers. Encryption tabulates single levels and decryption follows one witness path. Exponential proof-only prefix tables affect reduction time and hardness requirements. The fixed-size scan does not establish that all hardness and correctness conditions admit polynomial parameters for arbitrary inputs.

~~~python
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
    prefix_count = 1
    prefix_gain = 0
    prefix_gap = 0
    error_sum = 0
    power = 1
    scaled = 0
    for j, arity in enumerate((1024,16,1024)):
        prefix_count *= arity
        energy = 24 * prefix_count
        error_sum += power
        power *= n * variance
        if j < 2:
            prefix_gain += L[j]
        table = cs(2*n*m*energy*n*n*error_sum)
        scaled += table << (prefix_gap + prefix_gain)
        if j < 2:
            prefix_gap += max(8,L[j]*lg(1+L[j]),64+lg(192)+prefix_gain+L[j])
            next_arity = (16,1024)[j]
            shift = cs(2*n*m*energy*n*n*power*next_arity)
            scaled += shift << (prefix_gap + prefix_gain)
    f = max(prefix_gap, 68+lg(scaled))
    def z(N):return cs((68+lg(6*N)+3)//4)
    A=z(C*m)*sigma
    scalar=z(2064*(n*n+r*m+n*m))
    residual=scalar<<f
    for i in (1,2):
        residual=m*A*residual+24*(n*factor)**i*scalar*n
    if 16*(residual+1)>1<<K:return None
    bits=min(K,lg(2*A+1))
    return (1024*K*m+bits*m*C,K,a,digits,base,n,M,factor,m,sigma,bits,f)




rows = []
for a in range(1,257):
    for K in range(512,3073):
        row = trial(K,a)
        if row is not None:
            rows.append(row)
            break
print(len(rows), min(rows), min(row for row in rows if row[2]<=20))
print('previous point with new widths',trial(1385,116))

# Direct expansion of three scalar tree levels, with independent symmetric signs.
from itertools import product
for height in (1,2,3):
    amplitudes = (2,3,5)[:height]
    square_sum = count = 0
    for signs in product((-1,1),repeat=2*height):
        value = 0
        for i in reversed(range(height)):
            value = signs[i]*amplitudes[i]*value + signs[height+i]
        square_sum += value*value
        count += 1
    theory = 0
    for amplitude in reversed(amplitudes):
        theory = 1 + amplitude**2 * theory
    assert square_sum == count * theory
for m in (255139270836,min(rows)[8]):
    print('columns, dense Dec multiply-adds',16*m+1024*34,m*m+34*m)
~~~
