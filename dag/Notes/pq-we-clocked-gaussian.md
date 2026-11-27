---
title: A worst-case clock for shifted scalar Gaussian draws in lattice WE
refs: [definition:WE_CircuitSAT, note:pq-we-compiler-transport]
tags: [witness-encryption, sampling, complexity]
---

Consider one encryption subroutine that requests an integer with weights exp(-pi ((j-c)/s)^2), for rational c and rational s >= 1 given in binary. The bounded algorithm below approximates that law within total variation 2^-b. Both the bit clock and random tape length are polynomial in b and the input bit lengths, including for s exponentially large in its encoding length. It requires no table of size proportional to s. Centered scalar sampling occurs in algorithms such as [GPV basis sampling](https://web.eecs.umich.edu/~cpeikert/pubs/trap_lattice.pdf). Applying this result to an entire preimage sampler requires checking the scalar interface and all basis computations in the chosen implementation.

**Proposal.** Write L = ceil(s), P for the next power of two at least L, and m = floor(c). Choose a shell r with probability 2^(-r-1) for 0 <= r < t, rejecting the missing mass. Choose one side fairly and i uniformly in [0,P), rejecting i >= L. Propose m-rL-i on the left and m+1+rL+i on the right. With w(j) denoting its Gaussian weight, accept with probability 2^r w(j). The distance to c is at least rL, so this probability is at most one. Each retained integer then has joint proposal-and-acceptance mass w(j)/(4P). On a successful exact trial the conditional output law is the Gaussian restricted to the retained interval.

**Error budget.** Each excluded shell r >= t has at most 2L points and each weight is at most exp(-pi r²). The combined omitted mass is at most 4L exp(-pi t²) by geometric summation. The retained mass is at least L/32 since [c-s,c+s] contains at least L integers of weight at least exp(-pi)>1/32, and t >= 2 includes those points. The omitted probability is at most 128 exp(-pi t²) <= 128 times 2^(-4t²). Choose 4t² >= b+9. Since P < 2L the ideal per-trial success probability exceeds 1/256. A cap K = 256(b+2) leaves probability at most exp(-(b+2)) of returning the fallback. Finally choose p = b + bitlength(K) + 4. Use a p-bit threshold within 2^(1-p) of the scaled weight. Coupling trials with identical proposals and uniform coins costs at most K times 2^(1-p) in total variation. Summing omission, timeout and rounding gives less than 2^-b.

**Threshold arithmetic.** For v = ((j-c)/s)^2 the routine threshold(v,h) outputs an integer within 2 units of 2^h exp(-pi v). For d = bitlength(ceil(4v)), the scaled exponent is in [0,1]. At guard precision g = h+d+5, Machin's identity and the alternating arctangent series approximate pi to error below 2^-g. The exponential Taylor remainder at the scaled input is below 2^-g. Round the scaled input down on the g-bit grid. Compute the series as a rational, project to [0,1] and round down on the g-bit grid. Across d rounded squarings, the map x to x² on [0,1] amplifies errors by at most two per step. The rounding and Taylor contribution before the final h-bit floor is at most 4 times 2^(d-g). The error attributable to pi is at most v times 2^-g by the Lipschitz bound for exp(-x) on nonnegative inputs. The final floor adds less than one h-bit unit. For the shell coin use h = p+r and read the threshold in units of 2^-p. The shell bound gives v <= ((tL+1)/s)^2 = O(t²). All loops and rational intermediate bit lengths are polynomial; for example denominators in the Taylor partial sum divide the input denominator raised to the series degree times its factorial. The work per trial has no linear dependence on the numeric width s.

**Encryption accounting.** For at most Q >= 1 sequential scalar calls, including adaptive centers, choose b = lambda + ceil(log2 Q) + 2. Conditional coupling up to the first mismatch bounds the total change in the encryption law by 2^(-lambda-2). This adds at most that much to any fixed-witness decryption failure probability, and at most twice that much to the difference of acceptance probabilities between two message experiments, including quantum postprocessing of a classical ciphertext. Ciphertext framing and decryption work are unchanged. The sampler consumes at most K(t + ceil(log2 L) + 1 + p) bits per call. Any ideal GPV approximation error, approximation of algebraic centers or widths, trapdoor-generation error and dependence on the trapdoor quality require separate budgets. No reduction from the registered assumptions or end-to-end WE implementation is claimed here.

**Checks.** The reference implementation was checked against 100-decimal-digit exponential evaluations at 336 threshold inputs, with 27 complete sample paths and nine forced cutoffs. A separate check summed the actual finite-threshold proposal masses and the geometric timeout term for 27 combinations of center, width and error target. Each computed output law met its budget against a Gaussian normalized on a window extending 64L from the center. These numerical checks complement the analytic infinite-tail estimate.

~~~python
from fractions import Fraction as F
from functools import lru_cache
from math import ceil, isqrt

@lru_cache(None)
def pi_approx(bits):
    # For both arctangents the alternating remainder is below 5^(-2N-1).
    N = bits + 4
    def atan_inv(k):
        return sum((F((-1)**j, (2*j+1)*k**(2*j+1)) for j in range(N)), F(0))
    unit = 1 << (bits+2)
    return F(int((16*atan_inv(5) - 4*atan_inv(239))*unit),unit)

def threshold(v, p):
    # v = ((j-center)/width)^2. Return a p-bit coin threshold.
    d = ceil(4*v).bit_length()
    guard = p + d + 5
    x = pi_approx(guard)*v/(1 << d)
    unit = 1 << guard
    x = F(int(x*unit),unit)
    term = total = F(1)
    for i in range(1, guard+3):
        term *= -x/i
        total += term
    a = max(0,min(unit,int(total*unit)))
    for _ in range(d):
        a = a*a//unit
    return a >> (guard-p)

def sample(center, width, b, bits):
    # Exact rational input, width >= 1, b >= 1. bits(k) supplies k uniform bits.
    assert width >= 1 and b >= 1
    t = isqrt((b+12)//4)+1
    L = ceil(width)
    qbits = (L-1).bit_length()
    trials = 256*(b+2)
    p = b+trials.bit_length()+4
    mid = center.__floor__()
    for _ in range(trials):
        shell = t-bits(t).bit_length()
        if shell == t:
            continue
        idx = bits(qbits)
        if idx >= L:
            continue
        k = shell*L+idx
        j = mid-k if bits(1)==0 else mid+1+k
        v = (F(j-center)/width)**2
        if bits(p) < min(1<<p,threshold(v,p+shell)):
            return j
    return mid
~~~
