---
title: "Fresh samples under a global shortness condition"
refs: []
tags: [lattice-attack]
---
*Moved from `docs/research/wall1_fresh_samples.md` (core v0.1.2).*

# Fresh samples under a global shortness condition

Disjoint batches can be independent given the shared secret before selection. If the ensemble is then conditioned on the **total** squared length of the plant, that independence requires a new proof. The distinction already occurs with a fixed secret, two samples, and no reduction decisions.

## Conditional law

Fix the secret. Write the independent batches as random variables X and Y, with nonnegative squared-error contributions D(X) and D(Y). Subtract the fixed contribution of the secret and embedding coordinate from the squared-length cutoff and call the remaining budget B. Put F(t) = Pr[D(X) ≤ t]. In a discrete model with positive probability of passing the cutoff, the conditional mass of Y at y is

    Pr[Y = y | D(X) + D(Y) ≤ B]
      = Pr[Y = y] F(B − D(y)) / Pr[D(X) + D(Y) ≤ B].

Indeed, at fixed y the cutoff is precisely D(X) ≤ B − D(y), and independence gives the numerator. After observing X = x as well, the law of Y is its original law truncated to D(Y) ≤ B − D(x), provided this event has positive probability. Thus even the decision to record only the norm spent on the first batch can change the next batch's law.

## Two-sample example

Take q = 5, one fixed scalar secret s = 1, independent uniform design coefficients A₁,A₂ in the field, and independent uniform errors E₁,E₂ in {0,1}, independent of the coefficients. Set bᵢ = Aᵢs + Eᵢ modulo 5. The marked embedding vector with coordinates (E₁,E₂,s,1) has squared norm 2 + E₁ + E₂. Condition on squared norm at most 3. The three surviving error pairs (0,0), (0,1), (1,0) have equal probabilities. For this fixed-secret example the bit T indicating b₁ ≠ A₁ is observable from the first batch alone. Then

    Pr[b₂ ≠ A₂ | cutoff]        = 1/3,
    Pr[b₂ ≠ A₂ | cutoff, T = 0] = 1/2,
    Pr[b₂ ≠ A₂ | cutoff, T = 1] = 0.

The unconditional-on-T fresh marginal is therefore wrong on both branches. The design coefficients themselves remain independent uniform under this cutoff, since the cutoff depends only on the errors. Likewise, fixing the entire error vector in advance leaves this source of design randomness intact.

## Consequence for the proposed argument

This counterexample concerns selection by a global norm budget. It gives no obstruction from that source when shortness holds throughout the support of the planting distribution. Even in that case, a statement about a fresh batch in its own coordinate space needs a separate geometric argument identifying its marked lattice with the quotient of the original lattice by the chosen prefix. Independence alone supplies no such map. Neither a sample count nor a block-size guarantee at β = 406 follows from the conditional-law calculation.


## Independent audit (Nov 2026)

Verdict: **correct** (exact re-enumeration with q = 5, s = 1, bit errors, cutoff `E1²+E2²+s²+1 ≤ 3`: probabilities 1/3, 1/2, 0;
the 25 design pairs keep equal mass under the cutoff). Notes: "b1 ≠ A1" abbreviates `b1 ≠ A1·s` with `s = 1`; the comparison is
with the cutoff marginal 1/3 (the uncut value is 1/2). No obstruction from this source when shortness holds on the whole support.
