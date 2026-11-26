---
title: Masked linear verifier sketches and a public rank obstruction
refs: [note:pq-we-syndrome-local-tests, definition:WE_CircuitSAT]
tags: [witness-encryption, coding, reduction]
---

Consider hiding correlated verifier features with linear secret sharing. Sample a uniform binary r-by-n matrix H, a uniform weight-w vector e, and publish s=He. Given x,H,s and fresh public coins, generate public binary matrices T,G with the same number of rows. Publish Y=Te+Gu for independent uniform secret u. Arbitrary efficient public processing of this transcript is allowed. The plaintext bit is masked with a fresh random inner product with e. The fixed search challenge consists solely of H,s; a solution of weight w with that syndrome is efficiently checked. Assume negligible success for nonuniform polynomial-size quantum circuits at the chosen parameters. This is a conditional analysis; no parameter hardness is established here.

**Counting the missing bits.** Let K=ker H. For any particular e the law of Y is uniform on Te+im G. As e ranges over the entire affine solution space for s, the possible cosets form an affine space of dimension

    d = rank([T Kbasis | G]) - rank(G),

where Kbasis has columns spanning K. Restricting to the prescribed weight can only shrink this set. Solve for one e0 with He0=s, select d columns of T Kbasis extending a basis of im G, and guess d fair coefficients on those columns. Add Te0 and fresh Gu. For each fixed true error the guess hits its coset with probability exactly 2^-d, and conditional on the hit the transcript has the exact encryption law. All matrix work uses polynomially many bit operations. Hundreds of output bits can therefore cost just one guessed bit if their residual dependence is one-dimensional.

**Security on false instances.** If d <= k = O(log lambda) except with negligible probability on every false instance (polynomial size in lambda), auxiliary-input inversion with a true transcript is still hard. Run any proposed inverter on a guessed transcript when d <= k. Its success on the fixed challenge is at least 2^-k times its true success restricted to that event. This lower bound uses nonnegative recovery probability, so incorrect guesses cannot cancel correct guesses. To hide one fresh parity, first apply classical Goldreich-Levin list reconstruction with the true classical transcript fixed throughout each reconstruction, then guess the transcript for that inverter. A quantum distinguisher on classical inputs can be restarted with fresh work registers and classical nonuniform advice on each query. Any listed weight-w preimage can be checked. The same guessing argument permits a nonlinear generator with a k-bit descriptor if, for each challenge and true error on false inputs, the true feature law is a public sampler given that descriptor. A descriptor may also depend on public coins drawn before the guess. These are sufficient conditions to prove about a construction, not additional computational hardness assumptions. [Goldreich and Levin](https://www.wisdom.weizmann.ac.il/~oded/gl.html)

**A public decision procedure rules out the plain rank strategy for general NP under standard complexity conjectures.** Suppose every true instance has a fixed polynomial-length witness recovering e from the transcript with probability at least 1-delta, for delta <= 1/4. Fix such an instance and hardwire its witness in a circuit for the fixed game. If a=Pr[d <= k], guessing as above gives inversion probability at least 2^-k max(0,a-delta). Thus a <= delta + negligible for k logarithmic under the stated nonuniform hardness. This holds uniformly across bounded-size true instances: any infinite sequence of exceptions could be hardwired as classical advice. On false instances the proposed rank proof requires a >= 1-negligible. A classical algorithm can sample H,e and public coins itself and compute d by elimination, accepting exactly when d > k. With an explicit computable threshold and uniform sampler this is a bounded-error polynomial-time decision procedure for CircuitSAT (take lambda equal to padded input length and handle finite exceptions). Hence an efficiently observable low-rank/high-rank split would put NP in BPP. This conclusion concerns the proposed proof via public rank and high-success error recovery; it does not exclude other proofs for masked sketches, or mere parity decoders without error recovery.

For another design the meaningful target is a small set of hidden descriptors on false inputs whose size cannot be read off from public matrices. One precise possibility is to exploit the intersection with the weight-w sphere that the rank bound discarded: the set of attainable cosets can be much smaller than 2^d. Cardinality alone does not provide a sampler that hits the true coset. A proof would need an efficient method given only H,s,x that hits it with inverse-polynomial probability on false instances, and a correctness construction on true ones. Neither follows from sparsity alone.

The exhaustive example below counts both the guessed and the true coset distributions, including singular matrices, for two-bit errors and one-bit masks. It enumerates all weights by checking every error separately.
~~~python
from collections import Counter
from itertools import product

def apply(rows, e):
    return sum(((row & e).bit_count() % 2) << i for i, row in enumerate(rows))

checks = 0
for h in range(4):
    for rows in product(range(4), repeat=2):
        for g in range(4):
            mask = {0, g}
            for e in range(4):
                fiber = [v for v in range(4) if apply([h], v) == apply([h], e)]
                guessed = Counter(apply(rows, v) ^ z for v in fiber for z in mask)
                true = {apply(rows, e) ^ z for z in mask}
                space = {apply(rows, v) ^ z for v in range(4)
                         if not apply([h], v) for z in mask}
                cosets = len(space) // len(mask)
                assert cosets in (1, 2, 4)
                assert sum(guessed[y] for y in true) * cosets == guessed.total()
                assert len({guessed[y] for y in true}) == 1
                checks += 1
print(checks)
~~~
