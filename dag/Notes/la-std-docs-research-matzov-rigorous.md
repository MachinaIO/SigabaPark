---
title: "What survives modulus switching in the Pouly–Shen proof?"
refs: []
tags: [lattice-attack]
---
*Moved from `docs/research/matzov_rigorous.md` (core v0.1.2).*

# What survives modulus switching in the Pouly–Shen proof?

The DFT already appears at the end of the proof of Theorem 6. Group terms with the same frequency in a table and apply the finite Fourier transform. Linearity gives the same sum of characters at each guess, including when several samples occupy the same bin. Taking real parts gives the cosine score. This identity also holds on the smaller group after rounding. It gives scores indexed by residues modulo the smaller modulus. Distinct integer guesses with the same residue have identical rounded scores, so exact recovery from those scores alone requires an injective restriction on the candidate set or additional information. [Pouly–Shen, §4.2](https://eprint.iacr.org/2023/1508)

## The missing inequality

Fix the instance and draw the list independently from the lattice Gaussian in Theorem 6. In its proof the unrounded normalized score at guess u is exactly the real part of the empirical characteristic function evaluated at the fixed argument b − A_guess u. Lemma 7 identifies its expectation with a periodic Gaussian. Lemma 9 separates the value at the true guess from those at the false guesses. Rounding a projected frequency is nonlinear in the sampled vector. Substituting this frequency in the character breaks the fixed-argument identity used to invoke Lemma 7. Rounding the entries of the public matrix *before* projection is a different experiment. There the perturbed argument is fixed, but its displacement from the lattice must enter the distance bounds of Lemmas 8 and 9.

For a finite candidate set U containing the truth, let Δ be a lower bound on the unrounded population score gap supplied by the geometric hypotheses. Suppose each normalized rounded score differs pointwise from its unrounded counterpart by at most B, and evaluation has uniform absolute error at most ε. If Δ > 2(B + ε + d), for d > 0, the computed maximizer is correct except with probability at most 2|U| exp(−Nd²/2). Indeed each unrounded summand lies in [−1,1]. Hoeffding at each candidate and a union bound give uniform error at most d outside this event. Each of the two scores in a comparison can then move by at most B + ε + d. This proof needs independent draws with the exact marginal law D_{L⊥q(A_dual),qs} (so that E[cos] equals the periodic Gaussian of Lemma 3/7); B and ε must hold surely, or their failure probabilities must be added.

For projected nearest rounding of both the target phase and the guessed frequency coordinates to multiples of 1/p in turns, a fixed integer lift u incurs at most (1 + ‖u‖₁)/(2p) turns of error by the triangle inequality. Since cosine in turns is 2π-Lipschitz, one may take B = min(2, π maxᵤ(1 + ‖u‖₁)/p). If only frequencies are rounded, omit the 1. This deterministic sufficient condition can be vacuous. An expected attenuation derived from a Gaussian variance cannot replace B in that argument without controlling the true and false population scores under their joint input law. The target-rounding convention matters even at u = 0.

## Reading the estimator

The local port in python/lwemodel/dual_hybrid.py implements the upstream MATZOV class. The upstream DualHybrid class has a separate sparse-secret path. The following distinctions matter when interpreting their outputs. [Upstream source](https://github.com/malb/lattice-estimator/blob/main/estimator/lwe_dual.py)

- Nf models the projected noise and rounding through exponential factors using standard deviations. Projected rounding errors share the public instance and sampled vector. Even two equal frequencies have equal rounding errors. Marginal variances alone determine neither a characteristic function nor its product over coordinates.
- Nf fixes μ = 1/2, drops asymptotic terms, and charges a multiple-candidate factor involving Hf and log p. The code supplies a sample-count expression, with no explicit joint law for guess scores. Independence across guesses is unnecessary for the union bound above. Attributing an explicit independent-score simulation to the estimator would misdescribe the source.
- Hf, the enumeration multiplier and its prefactor depend only on the standard deviation. They do not specify a candidate set with a certified coverage probability. For iid CBD coefficients, X + η is binomial with 2η trials and probability 1/2, since complementing each subtracted fair bit again gives a fair bit. Thus any candidate set has exact mass equal to the sum of its product masses. The count of nonzero entries among k coefficients has law Binomial(k, 1 − binom(2η,η)/4^η). Uniform fixed-weight support instead gives a hypergeometric block weight by counting subsets. For a balanced-sign requirement one must count positive and negative slots separately.
- Nf uses a predicted vector length and cost uses a short-vector sampler model. Neither certifies independent discrete Gaussian draws at the required width. The arithmetic cost fixes multiplication at 1024 units and addition at 160. No precision guarantee accompanies these constants. The search fixes the default equation count to n and uses a coarse grid and early stopping. These are cost and optimization choices, independent of the DFT identity.

## Quantities identifiable for Kyber

Running python/matzov_rigorous.py gives the following comparison for the key-generation secret. Entropies are in bits per coefficient. Additivity gives exactly k times the Shannon entropy for k independent coefficients. An enumeration cost also depends on ordering, candidate masses and the stopping rule.

| Parameter set | η | CBD entropy | Estimator Hf | Excess per coefficient |
|---|---:|---:|---:|---:|
| Kyber512 | 3 | 2.33336203 | 2.33957684 | 0.00621480 |
| Kyber768 | 2 | 2.03063906 | 2.04709559 | 0.01645653 |
| Kyber1024 | 2 | 2.03063906 | 2.04709559 | 0.01645653 |

The corrected Pouly–Shen Table 1 reports estimated log₂ costs of 238, 347 and 478 respectively. The excesses above measure only the entropy term. Subtracting them from a total cost would mix different quantities. A per-assumption change in total bits is unidentified without specifying a replacement score law, sampler cost, candidate coverage and an optimization protocol. [Table 1 decomposition](pouly_shen_cost.md)

Qu and Xu describe a rational-lattice construction and CRT recovery. Their November 2026 abstract reports that their revised evaluation found no estimated cost reduction under the corrected settings. The perturbation inequality above is consistent with that observation, but proves neither a cost ordering nor a lower bound. The numerical evaluation was not independently reproduced here. [Qu–Xu, revised abstract](https://eprint.iacr.org/2025/859)


## Independent audit (Nov 2026)

Verdict: **sound**; Hoeffding/union over `U`, the triangle step, the rounding bound `B = min(2, π·max(1+‖u‖₁)/p)`, FFT
exactness and the lift collision are correct; the entropy excess (`MATZOV.Hf` = `log2(√(2πeσ²)/tanh(π²σ²))` vs exact CBD
entropy) reproduces (0.0062148 for η = 3, 0.0164565 for η = 2). Wording fixes applied above. Heuristics the list above omits:
* the upstream `dual_hybrid()` runs `DualHybrid`, not MATZOV; its non-sparse path uses `exhaustive_search`/`mitm` or
  `fft_solver` (GJ21), which carries an explicit "Independence Heuristic, cf. ia.cr/2023/302", a `√p` split of the success
  probability between enumeration and distinguishing, `support_size`, `m_required = 4·exp(4π²σ²)·(ln(2^t·size) − ln ln(1/p))`
  and cost `t·2^t + 4·m_required`; the sparse path adds `prob_drop`/`prob_amplify` repetitions;
* MATZOV's `Nf` adds `k_enum·Hf` (bits) to `k_fft·ln p` and `ln(1/μ)` (nats) — the local port copies this mix;
* `short_vectors` returns `ρ`, the output `N` and `β′`, which `cost()` discards; `Nf` instead assumes `β_sieve = β` with
  `√(4/3)·√(β/2πe)` and the GSA `δ^{m+k_lat−β}`;
* the noise factor `exp(4(ℓσπ/q)²)` and the cost formulas `T_fft = C_mul·k·p^{k+1}`, `T_table = 4·C_add·N`.
