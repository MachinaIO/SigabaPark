---
title: Exact empty-fiber probability for the succinct-LWE leaf setup over a prime field
refs: [definition:SuccinctLWE, note:pq-we-encryptor-setup-flooding]
tags: [witness-encryption, trapdoor-sampling, correctness]
---

For the challenger's setup in the C1 leaf lemma, let q be prime and σ positive. Condition on B and put d = n − rank(B). For independent uniform W, the conditional probability that trapdoorLaw returns some matrix is

    ∏_{i=0}^{ℓd−1} (1 − q^{i−m})   if ℓd ≤ m,
    0                              if ℓd > m.

The empty product is one. Each gadget block contains all standard basis columns (q ≥ 2). Hence all gadget columns have preimages exactly when the stacked matrix is onto. A nonempty fiber has positive Gaussian mass for σ > 0. The image of the diagonal B blocks is im(B)^ℓ. Quotienting by this image leaves a space of dimension ℓd. The m columns of W project independently and uniformly there because each fiber of the quotient map has the same cardinality. In any quotient basis, the resulting ℓd rows are independent uniform vectors in the m-dimensional row space of possible vectors. Conditional on the first i being independent, their span contains q^i vectors. Multiplication gives the formula.

For n ≤ m, averaging can be done without tabulating the rank distribution. Failure requires both B and W to lack full row rank. These events are independent. A uniform h-by-m matrix fails full row rank with probability at most U(h) = min(1, ((q^h−1)/(q−1)) q^{−m}), by counting one left-null event per projective line. Thus the unconditional probability of none is at most U(n) U(ℓn). This gains the factor U(n) over using W alone and remains informative when ℓn > m. The exact average is the expectation over B of one minus the displayed product, using success zero when ℓd > m.

For example, exhaustive enumeration at (q,n,m,ℓ) = (2,2,2,2) gives conditional failure probabilities 0, 5/8, 1 at deficiencies 0, 1, 2 respectively. The two challenge laws use the same marginal for (B,W,T), so the event contributes to leaf correctness accounting and has zero distinguishing advantage on its own. A Lean formulation can separate the deterministic image criterion, uniformity under the quotient, and the finite-field rank count.
