---
title: Exact NO hiding and the correctness cost of a Fourier mask for syndrome decoding
refs: [definition:WE_CircuitSAT, note:pq-we-code-list-features]
tags: [witness-encryption, coding, construction, complexity]
---

Use the binary decoding relation H x=y, |x|<=2r<=n with n columns and k rows. General decoding with a weight threshold is a classical NP-complete problem ([Berlekamp, McEliece and van Tilborg](https://authors.library.caltech.edu/records/aw9vs-ann16)). The following construction treats the even threshold. Its repetition cost depends on r,n.

Let S be the radius-r Hamming ball in F2^n and V its volume. Sample a binary noise vector e with mass

    p(e) = (sum_{u in S} (-1)^(u.e))² / (2^n V).

Orthogonality normalizes p. The expectation of (-1)^(e.x) is b(x)=|S intersect (S+x)|/V by expanding the square. In particular b(x)=0 for |x|>2r. To encrypt one bit mu, sample uniform s in F2^k and send (H^T s+e, y.s+mu). A witness x extracts mu+e.x, correct with probability (1+b(x))/2. Repeat with fresh coins for the same message and take majority. The ciphertext length is T(n+1) bits. With b_min the minimum overlap ratio for |x|<=2r, T>=2 ln(1/delta)/b_min² gives error <=delta. This specifies algorithms even when T is superpolynomial.

**Exact NO law.** For frequencies (x,c) of the n+1 ciphertext bits, the Fourier coefficient equals (-1)^(c mu) b(x) times the indicator Hx=c y. All message-dependent characters have c=1. When the statement is false every such x has weight greater than 2r, so the two ciphertext laws coincide, jointly for any number of independent repetitions and against quantum tests. No random-matrix assumption on H is needed.

**Classical sampling.** At output weight j the character sum is
    A_j = sum_{l=0}^r sum_{u=0}^l (-1)^u binom(j,u) binom(n-j,l-u).
Use zero for out-of-range coefficients. Sample j with integer weights binom(n,j) A_j² of total 2^n V, then choose a uniform j-subset. Binomial tables, integer sums, and subset unranking use polynomial bit complexity. Exact sampling by rejection has polynomial expected time. A fixed-time approximation by capping each uniform-integer rejection routine after L attempts incurs at most 2^(1-L) per noise draw (two routines, success at least one half per attempt). Include the resulting T-fold loss if using that convention.

**The correctness bottleneck is quantitative.** At weight 2r both translated representatives have weight exactly r, partitioning the 2r support into halves. Hence b=binom(2r,r)/V. For n=128,r=8 it is about 8.4122e-9, with reciprocal square about 2^53.65 before accounting for target error. For fixed r the overlaps are positive for all authorized weights and V=O(n^r), giving polynomial repetition in that restricted family. At growing r this calculation gives no general polynomial bound.

Changing amplitudes within the same ball cannot substantially increase the worst boundary bias. For any complex unit vector f supported on S take the squared modulus of its normalized binary Fourier transform as the noise law. Its bias is the autocorrelation. Sum its absolute bias over shifts of weight 2r. Only disjoint weight-r pairs contribute. Bounding |f(u) f(v)| by (|f(u)|²+|f(v)|²)/2 gives at most binom(n-r,r), since each weight-r vertex has that many disjoint neighbors. Thus some boundary witness has absolute bias at most binom(n-r,r)/binom(n,2r)=binom(2r,r)/binom(n,r). Uniform amplitude on the radius-r *sphere* attains this boundary bound, although odd-weight witnesses then have zero bias. The bound concerns a common ball-supported amplitude and the parity decoder; it does not rule out different supports, statement-dependent preprocessing or other decoding statistics.

More generally for any amplitude support S the sufficient exact-hiding criterion is y outside H(S+S), while witness advantage is controlled by a shift autocorrelation. The ordinary ball makes the former automatic on NO instances. A construction using more structured supports would need both efficient Fourier sampling and an inverse-polynomial overlap on every required YES witness, or a separate computational argument for message-dependent characters outside the exact cutoff.

In fact the boundary value is the exact b_min for the ball. Compare two centers agreeing on a chosen coordinate with the pair obtained by flipping that coordinate in one center. For each fixed string on the other coordinates let a,b be its distances to the two restricted centers. Summing over the chosen bit, the loss in intersection size is (1[a<=r]-1[a<r])(1[b<=r]-1[b<r]), which is nonnegative. Starting from identical centers proves monotonicity in the separation. Thus both repetition count and encoding length can be computed from two binomial sums without searching for a worst witness.
