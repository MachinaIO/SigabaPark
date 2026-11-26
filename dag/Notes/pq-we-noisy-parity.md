---
title: Noisy parity ciphertexts for a syndrome promise and the scope of a decisional hybrid
refs: [note:pq-we-masked-syndrome, definition:WE_CircuitSAT]
tags: [witness-encryption, coding, correctness, reduction]
---

Consider a binary r-by-n statement matrix H and target s. Given a bit b, sample a fresh uniform r-bit vector a and independent Bernoulli(p) noise z in n coordinates. Send (H^T a + z, b + s^T a). A witness v with Hv=s and weight at most w recovers a noisy copy of b with bias at least rho^w, where rho=1-2p is positive and bias means twice the success probability minus one. For R independent encryptions of the same bit, majority failure is at most exp(-R rho^(2w)/2). At p=2^(-ceil(log2(4w))) for w>=1, rho^w >= 1-2pw >= 1/2, so R=8 lambda suffices for failure at most exp(-lambda). The ciphertext uses exactly R(n+1) bits. Dense binary matrix multiplication and exact dyadic sampling cost O(R(nr+n log(2w)+r)) bit operations and random bits within this bound. With a support list the decoder uses O(R(w+1)) bit accesses and polynomial index/count overhead.

**A sufficient NO promise.** Define Z_s=sum_{v:Hv=s} rho^(2 wt(v)). The distance in total variation between the two one-copy message distributions is at most sqrt(Z_s). To see this, take Fourier expectations of characters indexed by (v,t) in the two distributions. The difference vanishes unless t=1 and Hv=s, in which case it is 2 rho^wt(v). Parseval followed by Cauchy-Schwarz on the normalized densities relative to the uniform transcript proves the bound including the factor 1/2 in total variation. Independent repetitions cost at most R sqrt(Z_s). Thus Z_s <= 2^(-2 lambda)/R^2 gives statistical security even for quantum observers. This is a polynomial-size promise scheme and does not require calculating Z_s during encryption. The promise can also hold when s belongs to im H: for H=I and s of weight n it suffices that rho^n <= 2^-lambda/R. Conversely H=I with target weight w+1 has no weight-w-or-less witness, yet parity on its public support predicts the bit with bias rho^(w+1). This gives an explicit reason exact short-preimage nonmembership cannot replace the enumerator promise.

**Where a fixed decisional challenge would enter.** Suppose a uniform randomized map E_b(x,D) is defined on all instances. On the real fixed challenge D0 its output efficiently approximates honest encryption, including for a decoder with a fixed YES witness (exact sampling suffices). Assume D0 and D1 are indistinguishable for nonuniform quantum polynomial time. The efficiently samplable ideal distributions E_0(x,D1), E_1(x,D1) are then far on YES after amplification: the witness distinguishes by correctness and the two transitions preserve its acceptance. If the desired NO hybrid proves these ideal distributions statistically close on every NO instance, these two public samplers themselves reduce CircuitSAT to Statistical Difference. Thus this uniform hybrid strategy still implies NP contained in SZK. Moving the statistical calculation above behind a single public decisional hybrid cannot by itself evade that implication. [Sahai and Vadhan](https://salil.seas.harvard.edu/publications/complete-problem-statistical-zero-knowledge)

One alternative proof architecture is a reduction selected with classical advice depending on the NO instance (for polynomially bounded instances and nonuniform fixed-game hardness). Such advice may select a sequence of embeddings or trapdoors; the fixed challenge sampler still sees only the security parameter. Establishing its polynomial length, existence for every false circuit, and both endpoint laws would all be construction obligations. This distinction between a statement-dependent reduction and a statement-dependent hardness game matters here. No such embeddings have been proved for the ciphertext above.

The check uses exact integer masses at p=1/4. It verifies the Fourier bound on every binary 2-by-3 matrix and target, including empty solution sets, and the single-copy decoder bias for every witness.
~~~python
from itertools import product

def dot(a,b):
    return (a & b).bit_count() % 2

count = 0
for cols in product(range(4), repeat=3):
    for s in range(4):
        mass = [0]*16
        for a,z in product(range(4),range(8)):
            y = sum(dot(a,c)<<i for i,c in enumerate(cols)) ^ z
            mass[y + 8*dot(a,s)] += 3**(3-z.bit_count())
        den = sum(mass)
        tv_num = sum(abs(mass[y]-mass[y+8]) for y in range(8))
        enum64 = 0
        for v in range(8):
            syndrome = 0
            for i,c in enumerate(cols):
                if v >> i & 1:
                    syndrome ^= c
            if syndrome == s:
                enum64 += 4**(3-v.bit_count())
                bias_num = sum(m * (-1)**(dot(v,y%8) ^ (y//8))
                               for y,m in enumerate(mass))
                assert bias_num * 2**v.bit_count() == den
        assert 64*tv_num**2 <= den**2 * enum64
        count += 1
print(count)
~~~
