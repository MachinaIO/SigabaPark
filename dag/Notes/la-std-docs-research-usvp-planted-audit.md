---
title: "Audit of the planted plain-LWE second minimum"
refs: []
tags: [lattice-attack]
---
*Moved from `docs/research/usvp_planted_audit.md` (core v0.1.2).*

# Audit of the planted plain-LWE second minimum

**Verdict.** The finite-radius upper bound in `usvp_planted.md` holds for uniform independent entries of A over a prime field, with fixed integer e and s, radius R ≥ 0 and d ≥ 2. The numerical exponent is correct. The phrase “gives failure probability ≈” in `docs/PROOF_GAP.md` should read “gives an upper bound of approximately”. The proof supplies a geometric gap. Algorithmic recovery requires a separate guarantee.

## Counting and lifting

Substituting b = As + e gives Au = v, with u = y − ts and v = te − x modulo q. For a fixed integer triple the exact membership probabilities are

| Residues | Probability | Reason |
|---|---:|---|
| u ≠ 0 | q⁻ᵐ | In each independent row one coefficient is uniquely determined by the other n − 1. |
| u = 0, v ≠ 0 | 0 | The system is inconsistent. |
| u = v = 0 | 1 | Every row satisfies the equation. |

In the last case q divides each discrepancy zᵢ − tpᵢ before the final coordinate. Its absolute value is at most √(1+pᵢ²)√(zᵢ²+t²) ≤ √(1+B²)R by Cauchy–Schwarz on two distinct coordinates. Strict inequality with q forces every discrepancy to vanish. The last coordinate already equals t. Thus the deterministic points inside the ball are precisely the multiples tp. The strictness matters in general. With e=s=0, B=0 and R=q, a vector of length q on the first coordinate axis is a deterministic off-line point.

Let N count off-line lattice points in the closed ball. The cases above give Pr[N ≥ 1] ≤ E[N] ≤ q⁻ᵐ times the number of integer points in that ball. Each such point centers a half-open unit cube, all cubes are disjoint, and each lies within radius R+√d/2 by the triangle inequality. Comparing volumes gives the claimed bound. The normalization Gᵈ=qᵐ/V_d also agrees with the covolume since the syndrome map is onto through x. Correlations between points, including opposite signs, do not affect this upper bound.

## Successive minima and recovery

Two real-linearly independent vectors of norm ≤ R cannot both lie on the planted line. Conversely an off-line vector of norm ≤ R gives such a pair with p whenever ‖p‖ ≤ R. Here integrality of the last coordinate gives L ∩ ℝp = ℤp. Without the length assumption only the first implication is needed for the λ₂ bound.

On the event N=0, if ‖p‖ ≤ R then λ₁=‖p‖ and λ₂>R. More generally, if γ ≥ 1 and γ‖p‖ ≤ R, any nonzero γ-approximate shortest vector lies on the planted line. A primitive output must be ±p, and any other multiple can be normalized by its signed last coordinate. This establishes a sufficient uSVP gap conditional on the length comparison. It gives no BKZ approximation factor or success probability for adaptive projected windows. The probability law averages over A before observing b and assumes a plain uniform matrix. Conditioning on b or replacing A by a module-structured matrix requires another argument.

## Numerical and asymptotic checks

At d=1537 the squared lift test gives 10,000,000 < 11,082,241. Using log V_d = (d/2) log π − log Γ(1+d/2) gives G=2113.389668 and d log₂((1000+√1537/2)/G)=−1616.235838. Also ‖p‖ ≤ √(1536·9+1)=√13825, so this radius certifies a gap greater than 1000/√13825 on the good event.

For m=2n and q of order nᵃ, Stirling gives G/q of order n^(1/2−a/3), tending to zero for a>3/2. Also √d/G tends to zero. At any fixed fraction R=αG with 0<α<1 the lift test therefore holds eventually for bounded B, and the probability is at most cᵈ for any fixed α<c<1 eventually.

## Lean scope

In `SigabaNeoStd/Lattices/Planted.lean`, `planted_iff` proves the field identity, `affineCount` counts solutions for m right-hand sides given a feasible witness, and `lift_multiple` proves integer equality assuming coordinatewise congruences and strict discrepancy bounds. Dividing the feasible count by q^(nm) gives q^(−m rank X), as used for fixed tuples. The Cauchy–Schwarz step supplying the strict bounds, ball count, probability theorem, successive-minimum implication and numerical evaluation remain paper arguments.
Running `lake env lean SigabaNeoStd/Lattices/Planted.lean` succeeded. Each declaration reported only `propext`, `Classical.choice` and `Quot.sound`.
