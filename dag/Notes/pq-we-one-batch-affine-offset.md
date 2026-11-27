---
title: Same-sample-count LWE reduction for a batch of known coefficient offsets
refs: [definition:WE_CircuitSAT]
tags: [witness-encryption, reduction, cost]
---

For the Gaussian public columns in the Bonsai split of PR 111, consider
a known integer matrix H fixed before seeing the challenge columns, with
||H||_F/s <= b. The desired target experiment has centered public integer
X' of width s and Y'=-C X'+C H+E versus independent uniform responses.
The available fixed game gives the same number t of columns, X and
Y=-C X+E or uniform. View the iid public coefficients as one flattened
discrete Gaussian p on the integer lattice. Any retained common context
may fix H provided the conditional challenge has these laws. Use the
usual efficient view construction from the columns and responses.

**Reduction.** Propose x=X+H, keep Y unchanged, and run the target test
with probability min(1,w(x)/M), returning a fixed bit otherwise, where
w(x)=p(x)/p(x-H) and M>0 is public. This consumes exactly t columns once.
It is a distinguishing reduction with a common abort branch, not a sampler
that promises an output ciphertext every time. At proposed x both games
have precisely the corresponding target conditional response laws. The
original input X must not also be exposed by the required view.

Let g(x) be the difference of conditional acceptance probabilities of the
target test, so |g|<=1. Write delta=|E_p g|. Multiplying the achieved gap
by M gives the absolute signed gap integrated against min(p,M p(x-H)).
Its difference from delta is at most the discarded mass
E_p[(1-M/w)_+]. For all w>0, (1-M/w)_+ <= w/(4M).
Moreover E_p w=exp(2 pi ||H||_F^2/s^2) *exactly*: completing the
square gives a sum of Gaussian weights translated by H, whose normalization
is unchanged for integer H. Thus with K=exp(2 pi b^2) the fixed-game
gap is at least delta/M-K/(4M^2). The same inequality after averaging
holds for a common random context with the uniform norm bound.

For delta>0 take M=K/(2 delta), obtaining fixed-game gap >= delta^2/K.
Equivalently, with a fixed-game bound epsilon at the reduction's runtime,
the shifted advantage is at most exp(pi b^2) sqrt(epsilon), apart from
implementation precision. An explicit lower bound delta0 on the claimed
advantage can replace delta in the choice of M to get delta0^2/K. A
nonuniform reduction can hardwire a suitable threshold with slack, or
one may round M upward by a factor at most two at constant-factor loss.
The scalar acceptance coin needs controlled numerical accuracy; an
additive error nu in each world's final acceptance costs at most 2nu.
The proof assumes integer columns or a justified lifting step from residues.

**Budget.** At fixed-game advantage 2^-kappa the exponent certified by
this bound is kappa/2 - pi b^2/ln(2). For example kappa=256 and b=1
gives about 123.47 bits, before runtime, approximation and other hybrid
losses. For asymptotic nonuniform QPT security, b^2=O(log lambda) costs
only a polynomial factor times the square root of negligible advantage.
For t equal shifts h the squared budget is t||h||^2/s^2; a per-column
bound cannot be substituted for the aggregate. A sparse change of
columns can therefore meet the criterion even when t is large.

This removes the extra candidate-sample premise of per-column retries
for the stated reduction. To apply it to the frontier flip one still needs
the hidden update to be C H for the embedded secret, H known to the
reduction without inspecting X, and a correct simulation of all retained
public data. This step does not establish any of these for APG-direct.
