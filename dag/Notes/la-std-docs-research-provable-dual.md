---
title: "What the Pouly–Shen theorem certifies"
refs: []
tags: [lattice-attack]
---
*Moved from `docs/research/provable_dual.md` (core v0.1.2).*

# What the Pouly–Shen theorem certifies

Theorem 6 fixes the public matrix, secret, and error. Its probability is over the independent discrete-Gaussian draws comprising the dual-vector list. The algorithm recovers the guessed block of secret coordinates. Holding the list fixed and drawing a fresh error defines a different probability experiment. [Pouly and Shen, Theorem 6](https://eprint.iacr.org/2023/1508.pdf)

Write σ for the paper's sampling-scale parameter, τ = √(m/(2π))/σ, and λ for the minimum distance of the full primal q-ary lattice. The theorem requires full column rank, m ≥ n, λ ≥ τ + ‖e‖, and a Gaussian-weight gap strictly exceeding 2δ between radii ‖e‖ and λ − ‖e‖ − τ, at width 1/σ. The samples have width qσ on the dual kernel lattice of the unguessed columns. The failure bound is qᵐ 2^(−Ω(Nδ²)). The time with samples supplied is polynomial in m,n times (N + q to the power of the guessed dimension). Equation (21) separately charges for sampling. The hidden constants and polynomial prevent direct conversion into a certified gate count. [Pouly and Shen, §§4.2–4.4](https://eprint.iacr.org/2023/1508.pdf)

## The fixed-list obstruction

For a finite input law p and real phases θᵢ(x), write Cᵢ = cos θᵢ. Linearity gives E[Σ Cᵢ] = Σ E[Cᵢ]. The second moment is half the sum over all ordered pairs (i,j) of E[cos(θᵢ + θⱼ) + cos(θᵢ − θⱼ)]. For normalized p, subtract the square of the first moment to obtain the variance. The cross terms depend on the law of the common input. Repeating one vector N times multiplies the variance by N². Even prohibiting duplicates permits the distinct phases θ and −θ, whose cosines agree pointwise. A list containing only zero gives a constant score and exactly zero distinguishing advantage for every pair of input laws. Shortness and dual membership alone therefore cannot imply the proposed positive advantage.

The Lean namespace `SigabaNeo.DualMoments` proves the two moment formulas and the centered second-moment scaling for repeated phases. These finite-sum identities apply to arbitrary real weights and hence to every finite probability mass function. They do not assume independence.

## Estimator comparison

The repository reports classical log₂ cost estimates of 149.88, 214.29, and 288.53 for dual and 139.66, 196.37, and 262.34 for dual hybrid, in Kyber512/768/1024 order. Its MATZOV reduction model supplies costs and its dual model predicts score behavior. A bound on lengths output by reduction supplies neither the joint Gaussian sampling law in Theorem 6 nor the off-diagonal terms of a fixed-list variance. Consequently no certified difference in bits follows from that reduction hypothesis. The finite moment results also leave the error-law evaluation, threshold success probability, and bit cost open. [Repository estimator table](../LWE_ESTIMATOR.md#kyber)
