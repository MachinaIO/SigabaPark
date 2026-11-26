---
title: "Provable dual attacks: literature status (survey, Nov 2026)"
refs: []
tags: [lattice-attack]
---
*Moved from `docs/research/provable_dual_literature.md` (core v0.1.2).*

# Provable dual attacks: literature status (survey, Nov 2026)

Survey of whether any paper proves a dual attack on LWE with cost near the estimator (Kyber512 ≈ 2^150).
Most entries were checked from abstract pages only (ePrint PDFs not fetched); "claimed" marks unverified content.
The Pouly–Shen Eurocrypt 2024 slides were read in full.

**Bottom line.** No paper proves a dual attack on Kyber with cost close to MATZOV/estimator figures. In the
"provable" line only *correctness* (success probability) is proven; all concrete bit counts use heuristic cost
models (GSA-based BKZ, a discrete Gaussian sampler bound shown for BKZ-reduced bases under GSA, core-SVP).

| Paper | Proven | Remaining assumptions | Kyber512/768/1024 |
| --- | --- | --- | --- |
| Ducas–Pulles, CRYPTO 2023 (ePrint 2023/302) | negative: independence heuristic contradicts theorems; "contradictory regime" | — | MATZOV/GJ21 success probabilities overestimated |
| Pouly–Shen, EUROCRYPT 2024 (ePrint 2023/1508, rev. 2026-05) | correctness of a simplified dual attack with discrete Gaussian dual vectors, ‖e‖ ≤ λ1/2 | cost: BKZ model + sampler bound under GSA; needs ≈ 2n samples | slides 185/273/376; after 2026 fix ≈ 238/347/478 (inferred) |
| Qu–Xu, ASIACRYPT 2025 (2025/859) | modulus switching via Poisson summation | same cost framework | after the fix: no gain (abstract) |
| Qu–Tian–Wang–Xu (2026/2117) | projected sublattice sampling, sharper Banaszczyk | claimed provable | 26–46 bits below original Pouly–Shen |
| Li–Wang–Wang (2026/2166) | provable score bounds for MATZOV-style FFT dual (claimed) | heuristic cost convention | 210/300/410 |
| Li–Wang–Wang (2026/2186) | general dual lattice (≈ n samples) with FFT (claimed) | heuristic cost models | 216/317/426 |
| Bashiri (2026/2565) | explicit success lower bound, no heuristic (claimed) | one ML-KEM structure heuristic; rank assumption for best figures | 22–100 bits below first provable attack; "no threat" |
| Carrier–Meyer-Hilfiger–Shen–Tillich, CRYPTO 2025 (2022/1750) | analysis without independence assumption | experimental modelling + sieve/GSA cost | ≈ 139.5/195/260 (closest to MATZOV, not rigorous) |
| Laarhoven (arXiv 2609.37483) | asymptotic decision-BDD trade-off without heuristics | Haar-random lattices; full dual ball given | none |
| Meyer-Hilfiger (2026/599), codes | doubleRLPN proven matching heuristic cost (claimed) | — | codes only |

**Relation to this repository.** `Dual/Assembled.lean` and `Dual/Sampler.lean` prove the same Fourier score test;
the difference lies entirely in the dual-vector source. The literature uses BKZ + discrete Gaussian sampling, whose
cost is only estimated heuristically (≈ 2^210–238 for Kyber512). Provable SVP/DGS (ADRS 2^{n+o(n)}) in dimension ≈ 500
would give far more than 2^200 (extrapolation, not in any paper). None of these results lowers H.

Sources: eprint.iacr.org/2023/302, 2023/1850, 2023/1508, 2025/859, 2026/1326, 2026/2117, 2026/2166, 2026/2186,
2026/2565, 2023/1238, 2022/1750, 2023/1460, 2026/599; arXiv 2312.00747, 2609.37483; doi 10.1515/jmc-2024-0028;
Pouly–Shen slides (iacr.org/submit/files/slides/2024/eurocrypt/eurocrypt2024/332/slides.pdf).
