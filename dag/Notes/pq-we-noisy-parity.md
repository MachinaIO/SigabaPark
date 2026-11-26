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

### Polynomial amplification from a constant NO promise

The NO promise can be relaxed to Z_s <= 1/4096, independent of lambda. Use the previous noise rate, so the raw YES crossover probability is at most 1/4 and the raw NO bit distributions have total variation q <= 1/64. The following explicit polarization preserves efficient witness decoding. Its purpose is a wider input promise; when the original exponentially small bound holds, the earlier linear repetition is cheaper. For the broader statistical polarization framework see [Sahai and Vadhan](https://salil.seas.harvard.edu/publications/complete-problem-statistical-zero-knowledge).

Start with nine independent raw encryptions of the same bit, decoded by majority. The per-bit failure f is at most Pr[Bin(9,1/4)>=5] and the message distance d is at most 9q. Then apply the following level t times. Encrypt a bit as two fresh uniform XOR shares conditioned on their parity, each under the preceding scheme, and decode by XOR. Independently repeat this pair three times for the same bit and take majority. All calls use independent coins. One pair has failure at most 2f conditional on either message. Its two transcript laws have difference (P0-P1) tensor (P0-P1) divided by two, so their total variation is exactly d^2. Consequently the new failure and distance satisfy

    f' <= 3(2f)^2,     d' <= 3d^2.

With u=max(12f,3d), each level gives u' <= u^2. The nine-copy initialization has u <= 3/5 by exact binomial counting. For t=ceil(log2(2 lambda)), u_t <= (3/5)^(2 lambda) <= 2^(-lambda). The ciphertext uses exactly 9*6^t*(n+1) bits per message bit, and encryption and decoding perform 9*6^t raw calls plus linear tree overhead, all polynomial. This construction also works directly under a constant bound on the true one-copy distance even if the Fourier upper bound is loose. A strict extension of the previous sufficient promise is H=I, w=1 and a target of weight six: its unique solution gives Z_s=1/4096 for every security parameter. The witness relation and short-preimage counterexample for arbitrary NO instances are unchanged.

On the preceding suggestion about NO-dependent advice, the existing [gap-structure argument](pq-we-gap-structure-routes.md) already handles arbitrary polynomial-size nonuniform simulation circuits. Merlin can supply the circuits; statistical matching of the endpoints on false inputs and the witness distinguisher on true inputs give a coAM protocol. Thus advice alone does not provide a general-NP embedding of the indicated statistical-simulation type unless NP is contained in coAM. The constant-promise result above uses no such embedding.

~~~python
from fractions import Fraction
from math import comb
f = sum(Fraction(comb(9,i)*3**(9-i),4**9) for i in range(5,10))
d = Fraction(9,64)
assert max(12*f,3*d) <= Fraction(3,5)
assert Fraction(3,5)**2 < Fraction(1,2)
for lam in (1,2,3,16,128):
    t = (2*lam-1).bit_length()
    assert 2*lam <= 2**t < 4*lam
    print(lam, t, 9*6**t)
~~~

### Shorter ciphertext via polynomial secret sharing and error correction

The expensive final levels can be replaced by a Reed-Solomon ramp from hiding to recovery. Choose N=32 lambda evaluation points, k=N/4, and m=ceil(log2(N+1)). Work over GF(2^m), and use N distinct nonzero points. An irreducible degree-m polynomial can even be selected deterministically by exhaustive search with polynomial-time irreducibility tests because 2^m=O(N). Encode the bit as the constant term of a polynomial of degree at most k with k independent uniform field coefficients. Evaluate at the N points. Encrypt each of the Nm resulting coordinate bits with the inner scheme above using only t levels, where t is the least nonnegative integer such that (3/5)^(2^t) <= 1/(16m). Thus both inner failure and inner distance are at most 1/(16m).

For YES, conditional on the full polynomial each decoded symbol is wrong with probability at most 1/16, independently across symbols. If fewer than N/4 symbols are wrong, unique Reed-Solomon decoding succeeds since the distance is N-k. For NO, write each inner distribution as the common pointwise minimum of P0,P1 plus its residual. This realizes the transcript by a channel which independently reveals its input bit with probability d and otherwise uses common randomness. Only the upper bounding channel needs to reveal bits; the decomposition need not be efficiently sampled. Exposing the whole symbol whenever any bit is revealed dominates the real transcript. Each symbol is exposed independently with probability at most 1/16. Any k field evaluations are statistically independent of the constant term by the invertible Vandermonde minor at distinct nonzero points. Both the error and the statistical distance are bounded by the probability of at least N/4 bad symbols. The union bound gives binom(N,N/4)16^(-N/4) <= (e/4)^(N/4) < 2^(-lambda) for the chosen N, where e is Euler's number.

The exact ciphertext length is 9*6^t*N*m*(n+1) bits. This is O((n+1) lambda log(2+lambda) (1+log log(2+lambda))^(log2 6)), improving the dependence on lambda from lambda^(log2 6). Field evaluation and unique decoding (e.g. Berlekamp-Welch with at most N/4 errors) have polynomial bit cost; symbols and field parameters are derived from lambda and need not be sent. The expression is an asymptotic improvement, without a claim of a small crossover or measured runtime.

### Linear ciphertext size with direct binary channel coding

Let the payload have h>=1 bits and B=max(lambda,h). The same raw YES crossover p0<=1/4 and NO distance d<=1/64 suffice for a block ciphertext of O((n+1)B) bits with no preliminary repetition. Encode a fresh uniform K-bit secret U as a binary linear codeword and apply the original noisy parity encryption independently to each code bit. Publish a fresh binary Toeplitz matrix seed for an h-by-K matrix F, and h masked bits M+FU. This uses the partial-observation principle of [Ozarow and Wyner](https://comlab.ecs.syr.edu/private/wiretap/Ozarow1.pdf).

Take m=max(16,ceil(log2(128B+1))), N the least even integer at least 64B/m, K=mN/2, and L=16mN. There are N distinct field points in GF(2^m). Use the K bits as coefficients of a degree <N/2 Reed-Solomon polynomial. Encode each evaluation by the same linear binary inner code with m input bits and 16m output bits. Fix a polynomial basis so field evaluation is binary linear. The exact length is L(n+1)+K+h-1+h bits. Every field and code description can be regenerated from B.

**Efficiently constructible inner code.** Select each m-bit generator column to minimize the running sum of (7/8)^wt over the partially encoded nonzero inputs. For a uniform independent column the expected sum is exactly 15/16 times the current sum. Enumeration of 2^m candidate columns and nonzero inputs with rational arithmetic is polynomial in B. At the end the sum is at most (2^m-1)(15/16)^(16m) <= (3/4)^m < 1, so the generator is injective. Decode each symbol by minimum Hamming distance, enumerating 2^m possible inputs. Given a fixed YES witness, the raw parity decoder induces an independent binary symmetric channel on the code bits. The probability that a particular alternative codeword of difference weight j ties or beats the true word is at most (2 sqrt(p0(1-p0)))^j <= (7/8)^j by the binomial Chernoff bound (also valid at p0=0). Thus each symbol fails with probability at most (3/4)^m. Reed-Solomon unique decoding recovers U if fewer than N/4 symbols fail. Conditional on U, independent symbol errors give a failure bound 2^N (3/4)^(mN/4) <= 2^(-mN/32) <= 2^(-2B) for m>=16. Apply the transmitted hash and unmask. Polynomial generation, nearest-neighbor search, and outer unique decoding are bit-polynomial; the enumeration gives large constants and this is not a measured implementation.

**Leakage bound.** Use the preceding common-part decomposition independently on the L bits. Revealing the selected code bits and their locations dominates the real observation. The number X of selected coordinates is stochastically dominated by Bin(L,1/64). A multiplicative Chernoff bound gives Pr[X>3L/128] <= exp(-L/640) <= 2^(-2B), since L>=1024B. Conditional on a selected set with at most 3L/128 coordinates, the exposed values impose at most 3L/128 independent linear constraints on U. For every nonzero row selector a, aF is uniform on K bits: its K coordinates are shifted copies of the same nonzero coefficient pattern evaluated on the independent seed diagonals, giving K independent linear forms by their distinct first nonzero positions. Hence the probability over F that its rows are dependent modulo the exposed rowspace is at most 2^(h+3L/128-K) <= 2^(-7B), since K=L/32. Otherwise FU is uniform on h bits even conditional on the exposure, the values and F. The total distance between encryptions of any two h-bit messages is at most 2^(-2B)+2^(-7B) <= 2^(-lambda). The polynomial-time algorithms and linear length cover the stated promise; no claim of a CircuitSAT compiler follows.

~~~python
from fractions import Fraction as Q
assert 2*Q(15,16)**16 < Q(3,4)
assert 2**6 * Q(3,4)**16 <= 1  # (3/4)^(m/4) <= 2^(-3m/32)
for b in (1,16,128,4096,65536):
    m=max(16,(128*b).bit_length())
    N=2*((64*b+2*m-1)//(2*m))
    L,K=16*m*N,m*N//2
    assert N<=2**m and L>=1024*b and K==L//32
    assert 128*(b+7*b) <= 128*K-3*L
    print(b,m,N,L,K)
~~~
