---
title: Amortize the projected AFV noise distribution over all output columns
refs: [definition:WE_CircuitSAT, note:pq-we-afv-sign-noise]
tags: [witness-encryption, predicate-encryption, lwe, cost]
---

In the projected AFV route of PRs #88–89, one base error vector x generates D=pm independent signed sums conditional on x. A table specific to x can amortize distribution construction across D draws. This note bounds the finite precision, support and fair-bit costs of doing that. The table is internal to encryption. It must be rebuilt for each independent base error vector. The ciphertext format and underlying decision-LWE premise are the same as in the parent note. The size example uses its hypothetical parameters.

**Compress the support before building the table.** Set a_j=|x_j|, S=sum a_j and Z=sum a_j B_j with independent fair bits. The original scalar law is (S-2Z) mod q. Compute the law of Z modulo a public power of two L. On a draw r lift it to the unique integer congruent to r in [ceil((S-L)/2),ceil((S-L)/2)+L). This recovers Z whenever |2Z-S|<L. Conditional on x, the moment bound cosh(t a_j)<=exp(t² a_j²/2) gives probability of a wrong lift <=2 exp(-L²/(2||x||²)) per draw (zero if x=0).

Let tau=134+ceil(log2 C), where C bounds the number of entries in the WE table. Abort encryption if ||x||²>R². For the independent rounded AFV base Gaussians of standard deviation sd before rounding, take R=ceil(sd sqrt(2m ln 2+4 tau ln 2)+sqrt(m)/2). Indeed the product Gaussian moment at 1/4 of the squared standard normal is 2^(m/2); Markov bounds the excessive unrounded norm probability by 2^-tau. Rounding adds at most sqrt(m)/2, and centered modular reduction can only decrease the norm. Take L at least R sqrt(2 ln(2D 2^tau)). A union bound over D exact draws costs another 2^-tau. These formulas presume the same ideal Gaussian source as the parent note; a finite Gaussian implementation needs a separate approximation budget.

**Compute the distribution with bounded integers.** Multiply the factors (1+u^a_j)/2 in the cyclic polynomial ring u^L=1, using a denominator Q=2^k. After each convolution, the folded integer coefficients v_i have sum Q². Replace coefficient i by the difference of consecutive floored cumulative sums in units of Q, obtaining integers w_i with sum Q. Each mass changes by at most 1/Q, so the rounding step costs at most L/Q in TV. Convolution with a probability law contracts TV; replacing both inputs costs at most the sum of their two errors. Grouping equal magnitudes and using repeated squaring is valid with this accounting: unfold the multiplication circuit into a binary tree with at most m leaves, counting a reused square input twice. Thus choose k=tau+ceil(log2(D(m-1)L)) for m>=2. For m=1 the dyadic base factor is exact at k=1. The D-draw product then costs at most 2^-tau in TV. Zeros can be skipped.

**Generate the draws.** Build a [Walker–Vose alias table](https://doi.org/10.1109/32.92917) for the L integer weights with denominator Q. Sample one uniform log2 L-bit index. Select its primary outcome with the slot's integer threshold divided by Q, else use its alias. Read independent bits only until the first mismatch with the k-bit threshold or until k bits are read (a tie selects the alias); handle thresholds zero and Q directly. At every slot this length is stochastically dominated by a geometric variable G on 1,2,... with success probability 1/2. At z=4/3, E[z^G]=2. For D independent draws, Pr[sum lengths>3D+3tau]<=2^D (4/3)^(-3D-3tau)<=2^-tau. Reserve D log2 L+3D+3tau logical fair bits; check remaining capacity before reading a bit and abort the whole encryption on overflow. Word refills can be charged separately. This fourth bad-event budget gives total TV at most 4 C 2^-tau <= 2^-132 across the WE table. The parent note's transfer to correctness and distinguishing gap applies.

**Example and computational price.** For m=2^19, p=117, sd=64 and C=41,923,871,289,682, the parameters are tau=180, R=54,944, L=2^20 and k=245. The reservoir is **1,410,859,548 bits per AFV entry**, versus 552,917,117,891 in the binomial-tree alternative and 32,160,715,112,448 explicit signs. This is a randomness bound. It does not establish a lower tape-machine cost N.

For F distinct nonzero magnitudes, binary powering and combining the results uses at most 2F(1+floor(log2 m)) cyclic products. Each exact product can use one integer multiplication with L byte-aligned coefficient slots of at least 2k+1 bits, followed by a linear fold and rounding pass. At the example parameters each packed multiplicand takes 62 MiB and the product up to 124 MiB, before multiplication scratch, alias records or interpreter overhead. A profile with many distinct magnitudes may spend more time in these products than the previous sampler spends on all its draws. The alias table itself can use L(k+1+log2 L) bits before packing overhead. On sequential tapes, one way to avoid D separate scans is to record random slot indices with output positions, sort by slot, merge once with the table while generating fresh threshold coins, then sort results back by position. Comparison sorting requires O(D log D) record comparisons and record movement; the additional tapes and preprocessing belong in any full cost bound. Neither the example-scale build nor a complete WE machine has been timed.

**Reproduction.** The Python listing performs exact cyclic integer convolutions, exhaustively compares small profiles to all sign assignments, and checks the reconstructed alias mass exactly. It also exercises modular lifting, calculates the bounds, and benchmarks a small instance with a noncryptographic PRNG. On one local run with m=256, L=512, k=96 and 32,768 outputs, building the table took about 10 ms and drawing took about 15 ms, at 10.30 logical bits per output. Grouped popcount used 200 bits per output and took about 25 ms with negligible setup. These small total times are close; the entropy saving alone predicts little about wall time. The diagnostic checks the budget after each draw; the bounded construction above checks before consumption.

~~~python
from math import ceil, log, sqrt, comb
from collections import Counter
from itertools import product

def cyclic(a, b, k):
    # Pack nonnegative coefficients in byte-aligned slots. The sum of all
    # coefficients before rounding is 2^(2k), so no slot can carry.
    L = len(a)
    width = (2*k+8)//8
    def pack(v):
        return int.from_bytes(b''.join(x.to_bytes(width,'little') for x in v),'little')
    raw = (pack(a)*pack(b)).to_bytes((2*L-1)*width,'little')
    folded = [0]*L
    for i in range(2*L-1):
        folded[i%L] += int.from_bytes(raw[i*width:(i+1)*width],'little')
    rem = 0
    for i, x in enumerate(folded):
        folded[i], rem = divmod(rem+x,1<<k)
    assert rem == 0 and sum(folded) == 1<<k
    return folded

def table(xs, L, k):
    unit = [1<<k]+[0]*(L-1)
    result = unit
    for a,c in Counter(abs(x) for x in xs if x).items():
        factor = [0]*L
        factor[0] += 1<<(k-1)
        factor[a%L] += 1<<(k-1)
        while c:
            if c&1:
                result = factor if result is unit else cyclic(result,factor,k)
            c >>= 1
            if c:
                factor = cyclic(factor,factor,k)
    return result

def alias(weights):
    L=len(weights); Q=sum(weights)
    w=[L*x for x in weights]
    small=[i for i in range(L) if w[i]<Q]
    large=[i for i in range(L) if w[i]>=Q]
    out=[(Q,i) for i in range(L)]
    while small and large:
        i=small.pop(); j=large.pop();out[i]=(w[i],j)
        w[j]-=Q-w[i]
        (large if w[j]>=Q else small).append(j)
    assert all(w[i]==Q for i in large+small)
    return out

for xs in ([], [0,0], [1]*10, [1,2,2,-5,8,0,1,2,9,3,5], [3]*17):
    L=8
    exact=Counter(sum(abs(a)*b for a,b in zip(xs,bs))%L for bs in product(range(2),repeat=len(xs)))
    for k in (3,7,19):
        Q=1<<k; w=table(xs,L,k); n=1<<len(xs)
        err=sum(abs(w[i]*n-exact[i]*Q) for i in range(L))
        assert err <= 2*max(0,len(xs)-1)*L*n
        if k>=len(xs):assert err==0
        recovered=[0]*L
        for i,(u,j) in enumerate(alias(w)):
            recovered[i]+=u;recovered[j]+=Q-u
        assert recovered==[L*x for x in w]
C=41923871289682; m=2**19; D=117*m; sd=64; tau=134+(C-1).bit_length()
norm=ceil(sd*sqrt(2*m*log(2)+4*tau*log(2))+sqrt(m)/2)
l=ceil(log(norm*sqrt(2*(tau*log(2)+log(2*D))),2))
k=tau+(D*(m-1)*(1<<l)-1).bit_length()
cap=(l+3)*D+3*tau
print(tau,norm,l,k,cap,D*m/cap)

# Reproducible kernel diagnostic. PRNG is for timing only.
from random import Random
from time import perf_counter
rng=Random(2718)
xs=[round(rng.gauss(0,2)) for _ in range(256)]
L=512; k=96; trials=32768
start=perf_counter(); w=table(xs,L,k); slots=alias(w); built=perf_counter()
def draw():
    i=rng.getrandbits(L.bit_length()-1); u,j=slots[i]
    if u==1<<k:return i,0
    if u==0:return j,0
    for t in range(k):
        b=rng.getrandbits(1); d=(u>>(k-t-1))&1
        if b!=d:return (i if b<d else j),t+1
    return j,k
charge=0
S=sum(map(abs,xs)); q=65537
def lift(r,S,L):
    lo=(S-L+1)//2
    return lo+(r-lo)%L
for S0 in range(65):
    for z in range(S0+1):
        if abs(2*z-S0)<L: assert lift(z%L,S0,L)==z
for _ in range(trials):
    r,used=draw();charge+=9+used
    if charge>12*trials+3*180:raise RuntimeError("reservoir exhausted")
    y=(S-2*lift(r,S,L))%q
end=perf_counter()
print('small profile: setup ms, draws ms, logical bits per draw',round(1000*(built-start),2),round(1000*(end-built),2),round(charge/trials,3))
# Exact explicit-sign baseline, grouped by magnitudes. Include setup.
start=perf_counter()
hist=Counter(abs(x) for x in xs if x)
grouped=perf_counter()
for _ in range(trials):
    y=sum(a*(2*rng.getrandbits(n).bit_count()-n) for a,n in hist.items())%q
print('grouped popcount: setup ms, draws ms, bits per draw',round(1000*(grouped-start),2),
      round(1000*(perf_counter()-grouped),2),sum(hist.values()))
~~~
