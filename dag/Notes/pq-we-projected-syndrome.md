---
title: Row compression of a syndrome channel and a fixed LPN hybrid
refs: [note:pq-we-noisy-parity, definition:WE_CircuitSAT]
tags: [witness-encryption, coding, reduction, efficiency]
---

Write J=[H|s] with r rows and n+1 columns. The raw encryption is J^T a plus (z,b), where a is uniform and z is independent coordinate noise with bias rho. Replacing r by k projected rows preserves every YES witness exactly: J(v,1)=0 implies PJ(v,1)=0. On NO instances projecting can instead create additional decoding vectors. For a uniform binary k-by-r projection P the exact expectation of the Fourier bound from the preceding note is

    E_P Z_{Ps}(PH) = (1-2^-k) Z_s(H) + 2^-k (1+rho^2)^n.

Each v with Hv different from s survives with probability 2^-k, without requiring independence across v. This distinguishes preserving a minimum distance from preserving the entire Fourier bound: avoiding *all* spurious vectors of weight at most d fails with probability at most 2^-k times the Hamming ball volume through d, but this union bound says nothing about the remaining Fourier mass. A large expected Fourier bound is not a lower bound on actual distinguishing advantage.

**A computational variant with exact YES cancellation.** Sample a public uniform k-by-r matrix P once per ciphertext, independently of the statement, and precompute PJ. For each raw encryption use a fresh uniform k-bit u and an independent r-bit error eta from a fixed efficiently samplable sparse distribution. Emit

    (PJ)^T u + J^T eta + (z,b).

Conditional on the public matrix, all pairs (u,eta) and z are independently refreshed. The correction includes the target column s. Thus parity on (v,1) has exactly the preceding YES law, regardless of the sparsity, correlation *within* eta, or rank of P. For NO, replace P^T u+eta by a uniform r-bit string using decisional LPN with a single fixed challenge law (P,Y), where Y is a noisy codeword or uniform. The reduction computes J^T Y and adds the independently sampled offset; the sign of b and all other coins are known to it. The winning predicate just checks the sampled game bit. Dimensions and noise must be a fixed public parameter family, with padding or separate parameter accounting for different input lengths; no entries of J enter the game. For T encryptions sharing P a single-challenge hybrid costs T times the one-challenge advantage: given P, the reduction samples both real and ideal auxiliary copies itself. After all replacements the public P is independent of the original transcript. For comparison of any two payloads the extra distinguishing gap is at most 2T times the single-challenge bound. This also works directly for the packed construction by sampling its codeword and hash before embedding. This is an actual fixed-game transition; it transfers whatever message hiding is proved for the original channel and does not establish that property on arbitrary NO inputs.

**Cost.** With eta a uniform vector of exact weight t, evaluating the correction takes t row additions. The relevant assumption is specifically fixed-weight decisional LPN at (k,r,t); Bernoulli noise uses its own game and has a variable number of row additions. In a dense bit-operation implementation preprocessing costs O(kr(n+1)), followed by O((k+t)(n+1)) binary arithmetic per raw copy, plus error sampling, z generation and the existing outer code. One can sample an exactly uniform t-subset using index sampling with expected polynomial time or introduce and account for negligible bounded-sampling error. The uncompressed dense multiplication costs O(r(n+1)) per copy. A saving in this multiplication count therefore requires k+t well below r and enough copies to amortize preprocessing. Public P adds kr bits to each complete ciphertext; the original linear packed length in B survives only when this cost is absorbed in O((n+1)B). No concrete hardness level, wall-clock acceleration, or total size decrease is claimed. The uniform random-code challenge is distinct from simulating an LPN oracle starting with a worst-case decoding input as in [Brakerski, Lyubashevsky, Vaikuntanathan and Wichs](https://eccc.weizmann.ac.il/report/2018/056/).

A necessary parameter screen follows directly from the game. Test whether the first k columns of P are independent, solve for u on those positions if they are, and check for residual weight t on all r positions. The real acceptance is at least prod_{i=0}^{k-1}(1-2^{i-k}) times binom(r-t,k)/binom(r,k), by the event that these positions contain no error. Under uniform Y the false positive probability is at most 2^(k-r) binom(r,t) by a union bound over secrets. Thus if the false positive bound is negligible and k,t=o(r), negligible fixed-game advantage requires kt/r to grow faster than log(lambda): the clean-position probability is exp(-(1+o(1))kt/r) and the rank factor is bounded below by a positive constant. In this regime k+t must grow faster than sqrt(r log(lambda)). This is only a necessary lower bound on the proposed per-copy row budget, not a sufficiency claim.

The exact enumeration checks every 2-by-3 binary input matrix, target, and 1-row projection with rho=1/2. It also checks all decomposed mask evaluations, including the target coordinate.
~~~python
from itertools import product
def dot(x,y):
    return (x & y).bit_count() % 2
def syn(cols,v):
    y=0
    for i,c in enumerate(cols):
        if (v >> i) & 1:
            y ^= c
    return y
def mass(cols,s):
    return sum(4**(3-v.bit_count()) for v in range(8) if syn(cols,v)==s)
cases=0
for cols in product(range(4),repeat=3):
    for s in range(4):
        projected=0
        for p in range(4):
            projected+=mass([dot(p,c) for c in cols],dot(p,s))
            for u,eta in product(range(2),range(4)):
                assert all(dot((p*u)^eta,c)==((u*dot(p,c))^dot(eta,c))
                           for c in (*cols,s))
        assert projected==2*(mass(cols,s)+125)
        cases+=1
print(cases)
~~~
