---
title: Moving a known coefficient offset into Gaussian public LWE columns in the Bonsai split
refs: [definition:WE_CircuitSAT]
tags: [witness-encryption, reduction, simulation]
---

In [PR 111 section 2](https://github.com/MachinaIO/SigabaPark/blob/d0cdda51bd1354fe7f0a5cbb9e08e57ac6a8a48b/dag/Notes/pq-we-exposed-root-reachable-lemma.md)
the reduction knows B1 and has a trapdoor for A2. C1 is the unknown
secret, and the challenge supplies X,Y=-C1 X+E or independent uniform Y.
Thus the source of the public X columns is a Gaussian challenge, not a
programmable uniform matrix. The independently appended-column lemma does
not by itself apply to this block. There is, however, a direct simulation
for an offset of the restricted form C1 h with known integer h.

**Required law.** For one column draw X' from the same centered discrete
Gaussian of width s on Z^m and obtain Y'=-C1 X'+C1 h+E. Its ideal version
has independent uniform Y'. Raw X must be visible to the reducer as an
integer draw, and the reducer can consume several independent candidate
columns with the same C1. Fix h independently of these candidates given
the retained context. Propose X'=X+h and keep Y'=Y. The real equation
already holds exactly, with precisely the original error. Correct the
visible column law by rejection depending only on X'. For target density
p(x) proportional to exp(-pi||x||^2/s^2) and proposal p(x-h), set

    w(x) = p(x)/p(x-h) = exp(pi (||h||^2-2<x,h>)/s^2).
    Accept with probability min(1,w(x)/M).

Put b=||h||/s, choose 0<eta<1 and log M=pi b^2+2 b sqrt(pi log(1/eta)).
Under p, Pr[w>M]<=eta. Indeed the centered discrete Gaussian projection
onto h has moment generating function at t at most exp(t^2 s^2 ||h||^2 /
(4 pi)): complete the square and use that Gaussian mass on a shifted
integer lattice is maximized at zero (Poisson summation). Apply Chernoff
to the negative projection. The admitted mass times M is
min(p(x),M p(x-h)), a subdistribution missing at most eta from p.
Hence the normalized accepted law is eta-close to p and success probability
is at least (1-eta)/M. With K fresh columns per desired output, first
success has failure probability at most exp(-K(1-eta)/M). For h=0 one
candidate suffices exactly. All logarithms here are natural.

Selection is independent of the corresponding error and of an ideal
uniform response, conditional on the fixed secret and retained context.
Discard unused challenges. Applying any common efficient postprocessing
(in particular the A2 trapdoor sampler on known offsets plus Y') costs no
additional statistical distance. Compute exposed B1 terms from X', not X.
Auxiliary values committed to the original X cannot be retained by this
argument. For t output columns with independent reserved batches, sum the
t per-column error bounds (including any coin approximation). At
eta=2^-lambda and b=O(1/sqrt(lambda)), M=O(1) and K=O(lambda+log t)
suffices for negligible total failure for polynomial t. This resource
bound uses a fixed LWE game with tK challenge samples; the cited lemma's
2m-sample concrete premise cannot silently supply that larger budget.
If only residues of X are supplied, an integer representative with the
correct conditional law must be available or wraparound bounded.

**What changed.** This transports a secret-dependent target difference
without knowing C1 h, altering the LWE error, or exposing a planted lift.
It requires the hidden part of the desired offset to factor through C1
with *known small coefficients*. In PR 113 the frontier comparison
involves a product with a different level's shared secret; no such
factorization in the PR 111 embedded C1 coordinates has been established.
Other public blocks need the same simulator and their own input-law check.
This lemma neither removes the original G E smudging term from PR 111
nor proves the non-co-located flip.
