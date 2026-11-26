---
title: "Pouly–Shen cost evidence for Kyber"
refs: []
tags: [lattice-attack]
---
*Moved from `docs/research/pouly_shen_cost.md` (core v0.1.2).*

# Pouly–Shen cost evidence for Kyber

> Status: updated with the fixed ePrint version (PDF supplied by the user). Section "Fixed Table 1, decomposed" below
> reproduces the corrected totals 238/347/478 within about 0.6 bits, component by component, and adds the omitted polynomial factors.

The authors describe the Kyber costs as rough estimates using an MCMC discrete Gaussian sampler. The archive dates their correction to May 28, 2026. An automated download of the revised PDF first failed (HTTP 403); the user then supplied the fixed PDF, and the section "Fixed Table 1, decomposed" below is based on it. [Revision history and authors’ abstract](https://eprint.iacr.org/2023/1508)

## What the probability bound measures

According to the repository’s reading of Theorem 6, the public matrix, secret and error are fixed. Conditional on the geometric separation and rank hypotheses, independent draws from the specified lattice Gaussian give a failure bound of the form $q^m 2^{-\Omega(N\delta^2)}$ for recovery of the guessed block. Here $m$ counts equations, $N$ counts dual draws and $\delta$ measures score separation. The stated time with the list supplied is $\mathrm{poly}(m,n)(N+q^{n_{\rm guess}})$. Neither expression specifies a numerical bit-operation count. The repository’s Lean fresh-sample theorem also draws fresh right-hand sides, which changes the probability space. [Theorem 6 reading](provable_dual.md) and [finite sampler analysis](dual_sampler.md)

A sampler analysis needs both an accuracy budget and a cost per draw. For example, if independent approximate draws are each within total variation distance $\epsilon$ of their targets, coupling bounds the additional failure probability by $1-(1-\epsilon)^N\le N\epsilon$. A marginal guarantee alone leaves dependence between successive MCMC outputs unaccounted for. The geometric series assumption models the reduced basis profile. A core-SVP estimate assigns a cost to reduction. Neither establishes the numerical mixing time or gate count for the basis actually obtained. A certified comparison would require bounds on preprocessing, joint sampling error, sampling time, and finite-precision score evaluation in a common operation model. The revised parameters and component costs are decomposed in the last section.

## Historical numerical comparison

The PS column transcribes the no-modulus-switching estimate on slide 9. The original paper’s Table 1 discussion explicitly omits polynomial factors. The estimator columns use the classical dual and dual-hybrid values recorded for the module-LWE instance without ciphertext rounding. Subtraction compares reported base-two logarithms at their displayed precision. The differences have no interpretation as certified security margins. [Authors’ slides](https://www.pouly.fr/data/slides/eurocrypt2024.pdf) and [repository estimator table](../LWE_ESTIMATOR.md#kyber)

| Kyber | PS (2024) | dual | dual hybrid | PS − dual | PS − hybrid |
| --- | ---: | ---: | ---: | ---: | ---: |
| 512 | 185 | 149.88 | 139.66 | 35.12 | 45.34 |
| 768 | 273 | 214.29 | 196.37 | 58.71 | 76.63 |
| 1024 | 376 | 288.53 | 262.34 | 87.47 | 113.66 |


## Fixed Table 1, decomposed (from the corrected ePrint version)

Source: the fixed ePrint version (banner: "The published version ... contains incorrect numbers in Table 1 due to a
mistake in the implementation of the estimator ... This version contains fixed estimates"), Section 4.4, formulas
(21)–(25), Table 1 (no modulus switching: Kyber512/768/1024 = **238 / 347 / 478**, `m = 1023/1519/2025`,
`n_guess = 19/29/39`, `β = 746/1129/1602`, `s = 0.09/0.11/0.11`). The authors' public estimator
(gitlab.inria.fr/apouly/dual-attack-estimator, `compute_cost`) was read (not executed). Note: its `reproduce_arctic` passes `True` as `quiet`, so it uses the arctic approximation of the MCMC cost; our script uses the exact product, which agrees with the approximation to 0.001 bits. `python/pouly_shen_cost.py`
is an independent reimplementation of its formula:

`rop = N·T_MCMC + q^{n_guess} + T_BKZ(m, β)`, `δ = e^{−m s² σ_e²/2}/100`, `N = n ln q / δ²`, `σ_e = √(2π)·stddev`,
`T_MCMC = ∏_i ρ_{‖b̃_i‖/(qs)}(ℤ)` with the GSA profile `‖b̃_i‖ = q^{n_dual/m} δ_β^{m−1−2(i−1)}`, and `T_BKZ` the
estimator's MATZOV (list-decoding, classical) model.

| Kyber | log2 δ | log2 N | log2 T_MCMC (per sample) | log2 q^{n_guess} | log2 T_BKZ | total (formula) | Table 1 | with explicit poly factors | explicit − est. dual | explicit − est. dual hybrid |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 512 | −62.98 | 137.98 | 98.30 | 222.32 | 237.45 | 237.98 | 238 | 262.92 | +113.04 | +123.26 |
| 768 | −89.95 | 192.50 | 154.78 | 339.33 | 345.24 | 347.60 | 347 | 375.53 | +161.24 | +179.16 |
| 1024 | −117.70 | 248.42 | 224.51 | 456.33 | 478.33 | 478.36 | 478 | 502.36 | +213.83 | +240.02 |

"Explicit poly factors" (our accounting, not in the paper, which states "all our complexity estimates ignore the
polynomial factors"): scoring `N·m` multiplications plus a DFT over `ℤ_q^{n_guess}` costing `q^{n_guess}·n_guess·log2 q`;
MCMC mixing `ln(1/ε)·Δ` steps per sample with `ε = 1/(100N)` (the paper requires `ε ≪ 1/N`) and `m²` operations per
step. These add 24.9 / 27.9 / 24.0 bits. (Forming `w_jᵀA_guess` costs about `N·m·n_guess`, not counted; it does not change the totals since `N·T_MCMC` dominates.) The MCMC mixing is `ln(1/ε)·(1/Δ)` steps in the paper's notation (eq. 23), and the cost uses the upper bound (25) on `1/Δ`. The estimator columns are this repository's dual / dual-hybrid values.

What is proven and what is not:
* **proven** (Theorem 6): success probability `1 − q^m 2^{−Ω(Nδ²)}` given exact independent samples from
  `D_{L_q^⊥(A_dual), qs}` and the geometric conditions; the `Ω` constant is not explicit in the theorem.
* **proven** (MCMC, the paper's Theorem 2 = [51, Theorem 1]): ε-closeness and the mixing time `ln(1/ε)·Δ·poly(n)` for a given basis.
* **heuristic**: `Δ` is evaluated with the GSA profile of a BKZ-β basis; `T_BKZ` is the MATZOV sieve model
  (`2^{0.2961β'+20.39}`); `λ1(L_q(A))` is taken at the Gaussian heuristic (supported by the paper's informal Corollary 2); the root-Hermite value `H_β` (eq. 37) is experimental; `σ_e = √(πη)` matches CBD by variance only.
* The analysis uses `m ∈ [3n/2, 2n]` samples (1023 for Kyber512); a Kyber public key provides `n` samples.
* BKZ dominates for Kyber512 (`2^{237.45}` vs `N·T_MCMC = 2^{236.28}`).

### Audit notes (independent audit, Nov 2026)

* Reimplementation matches `compute_cost` exactly (δ, N, σ_e, red_vol, `s_i`, `ρ_ℤ`, guessing term); `matzov_bits(β, m)`
  matches the estimator's MATZOV model term for term (LLL `d³` + `C²(d−β)·2^{a(β−d4f)+b}`, `C = 1/(1−2^{−a})`).
* Totals 237.98 / 347.60 / 478.36 versus Table 1 238 / 347 / 478: no single rounding reproduces all three (truncation gives
  237/347/478, rounding 238/348/478). Most likely the table came from optimizer runs with unrounded `s`, while the published
  `s` has 2–3 decimals (`∂log2 N/∂s ≈ 2500` bits per unit of `s` for Kyber512, so `0.0005` in `s` moves `N` by ≈ 1.25 bits).
* The estimator's `N = n ln q/δ²` drops the paper's `poly(m)` and uses `ln` instead of `log2` (eq. 19). With `m ≈ 2n` this `N`
  does not by itself make `q^m 2^{−Ω(Nδ²)}` small; a Hoeffding + union bound needs about `2m ln q/δ²` (≈ 2 more bits on `N`),
  lifting Kyber768's total to about 349. So proven success at exactly these parameters does not follow from Theorem 6 as stated.
