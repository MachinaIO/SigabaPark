---
title: "How far the proofs reach: proven attack costs against the estimator"
refs: []
tags: [lattice-attack]
---
*Moved from `docs/PROOF_GAP.md` (core v0.1.2).*

# How far the proofs reach: proven attack costs against the estimator

`H` is the floor of the cheapest attack in the lattice estimator's model
([LWE_ESTIMATOR.md](LWE_ESTIMATOR.md)). That model rests on heuristics. This file tracks, stage by
stage, which part of an attack's cost is proved without them, and how far the proved cost is from
the estimator's. Only results with no `sorry` and no `axiom` count; anything else is listed as
open.

## Stage 1: BKZ output quality without the GSA

**Proved in Lean** (`SigabaNeoStd/Lattices/Reduction/BKZ.lean`, `Reduction/BKZ/Profile.lean`, `Reduction/BKZ/Hermite.lean`;
axioms: `propext`, `Classical.choice`, `Quot.sound` only):

| Theorem | Statement |
| --- | --- |
| `BKZ.first_log_bound` | a Gram–Schmidt log-profile in which each block of size `k_i = min(β, n−i)` satisfies Hermite's inequality with constant `c` has Hermite factor `r_0 − S_n/n ≤ c (n−1)/(β−1) + c`, that is `Γ_β^{(n−1)/(2(β−1)) + 1/2}` with `c = ½ log Γ_β`, `Γ_β = max_{k≤β} γ_k` |
| `BKZ.hermite_cube` | Minkowski: every full-rank lattice in `ℝ^k` has a nonzero vector with `‖v‖² ≤ k · covol^{2/k}`, so `γ_k ≤ k` |
| `BKZ.projected_profile`, `BKZ.first_norm_bound` | the same bound from caller-supplied projected block data |
| `BKZ.reduced_first_norm_bound_covolume` | for a BKZ-β-reduced basis `b` of `L` (built with Mathlib's `gramSchmidt`; every projected block's first vector is shortest), `‖b_0‖ ≤ β^{(n−1)/(2(β−1)) + 1/2} covol(L)^{1/n}` |
| `BKZ.blockLattice_covolume`, `BKZ.basis_covolume` | the covolume of a projected block, and of the lattice, is the product of the Gram–Schmidt lengths |
| `BKZ.hermite_ball_linear`, `BKZ.gamma_half_nat_bound` | `γ_k ≤ (k+4)/π` for every `k ≥ 1` (from `Γ(k/2+1) ≤ ((k+4)/4)^{k/2}`) |
| `BKZ.reduced_first_norm_bound_covolume_ball` | for a BKZ-β-reduced basis, `‖b_0‖ ≤ ((β+4)/π)^{(n−1)/(2(β−1)) + 1/2} covol(L)^{1/n}` |
| `BKZ.reduced_approx_factor` | Schnorr's approximation factor: for a BKZ-β-reduced basis and every nonzero `v ∈ L`, `‖b_0‖ ≤ ((β+4)/π)^{(n−1)/(β−1)} ‖v‖` |
| `BKZ.hermite_blichfeldt` (`Reduction/Hermite2.lean`) | Blichfeldt: `γ_k ≤ (2/π) Γ(k/2+2)^{2/k}`, with corollaries `reduced_first_norm_bound_covolume_blichfeldt` and `reduced_approx_factor_blichfeldt` (machine-checked; axioms `propext`, `Classical.choice`, `Quot.sound`) |
| `BKZ.hermite_ball` | Minkowski with the ball volume: some nonzero lattice vector has `‖v‖ ≤ 2 (covol / V_k)^{1/k}`, `V_k = π^{k/2}/Γ(k/2+1)` |

**Open in stage 1:**

* The HPS theorem for polynomially many tours (`2 Γ_β^{(n−1)/(2(β−1)) + 3/2}`) and its tour count
  are not proved. Only the fully reduced case is.
* `γ_k ≤ k`, `γ_k ≤ (k+4)/π` and Blichfeldt's bound are proved in Lean.
  Kabatiansky–Levenshtein is open.

**What it gives the primal attack.** The worst-case approximation-factor bound for BKZ-β,
`‖b_1‖ ≤ γ_β^{(d−1)/(β−1)} λ_1` (proved in Lean with `γ_β ≤ (β+4)/π`: `reduced_approx_factor`), recovers the target when that factor times `‖(e, s, 1)‖` is below
`λ_2`. Here `λ_2` still comes from the Gaussian heuristic, the stage-2 target. The table gives the
smallest `β` (optimised over the number of samples) and its cost in the estimator's `RC.MATZOV`
model. The GSA column is the estimator's primal uSVP.

**Correction (block size `β ≤ d`).** The earlier version of this table reported `β` up to 6876. That
is invalid: Kyber gives at most `m = n` samples, so the embedding dimension is
`d ≤ n + m + 1` (1025 for Kyber512), and the theorems need `β ≤ d`. With `β ≤ d` enforced
(`python/proof_gap.py`), **no admissible block size exists for Kyber512/768/1024 under any of the
constants**: the proved `β`, `(β+4)/π`, the exact Minkowski ball, Blichfeldt, and even the
heuristic `β/(2πe)`. The worst-case approximation-factor route therefore gives no cost at all for
Kyber. At `β = d`, BKZ is an exact SVP call, and Schnorr's bound is loose there. Solving SVP
directly in dimension `d` is exactly the full-dimension sieve route below.

| Kyber | GSA (estimator) | worst-case BKZ route, any proved or heuristic `γ_β`, `β ≤ d` |
| --- | --- | --- |
| 512 | β = 406, 143.8 bits | no admissible `β` |
| 768 | β = 624, 204.9 bits | no admissible `β` |
| 1024 | β = 874, 275.1 bits | no admissible `β` |

The Hermite-factor bound that is proved (`first_norm_bound`) does not by itself recover the target
at any `β < 6000` for these instances. It does not use the shortness of the target.

**What this measures.** Even with `γ_β` at its heuristic value, the worst-case analysis costs about
440 bits more for Kyber512. The gap is the difference between the worst-case shape of a reduced
basis and its average shape on random q-ary lattices, which the GSA models. Closing it needs an
average-case analysis of BKZ on random q-ary lattices. That is an open problem: no theorem in the
literature predicts BKZ's output shape on random lattices.

The attacks that `H` takes into account are therefore not replaced by proven ones. Dropping the
heuristic attacks would raise `H` for Kyber512 from 139 to several hundred bits, an
overestimate. `H` keeps the estimator's model, and this file records the distance.

## Wall 1: the average-case BKZ profile on random `q`-ary lattices (in progress)

* **First step (new; [research/avg_bkz.md](research/avg_bkz.md); audited: passes for the stated ensemble, [research/avg_bkz_audit.md](research/avg_bkz_audit.md)).** For an i.i.d.
  uniform prime-field parity-check matrix, one fixed coordinate projection preserves an exact
  random modular-kernel law. Given that the prefix columns span `S`, the projected lattice is the
  modular kernel of independent uniform columns in the quotient by `S`. Before BKZ, the next
  Gram–Schmidt length of the coordinate-adapted basis is `q` with probability `1 − q^{r−n}` and
  `1` otherwise.
* **Obstruction.** Once the prefix spans the syndrome space, the projected lattice is exactly
  `Z^{d−t}`, the thin-shell-empty type. So random coordinate orderings and internal basis changes
  alone cannot enforce the sieve's statistics.
* Lean: `AvgBKZ.coordinateProjection` and `AvgBKZ.quotientColumnCount`. Axioms `propext`,
  `Classical.choice`, `Quot.sound`.
* **Part 2 (obstruction; [research/avg_bkz2.md](research/avg_bkz2.md)).** The exact law fails after one
  exact SVP selection. In dimension two the projected spacing lies strictly between 1 and `q` with
  probability `≥ (1 − 1/q)²`. Lean: `AvgBKZ.planeShortestSq`, `AvgBKZ.planeNormalSq`.
* **Part 3 (obstruction; [research/avg_bkz3.md](research/avg_bkz3.md)).** Few prefixes per BKZ run do
  not justify a union bound over fixed prefixes, because of selection bias: fixed-index failure `1/N`,
  yet a selecting run fails with probability 1. Lean: `AvgBKZ.diagonalSelectionCounts`,
  `AvgBKZ.diagonalWeightHalf`.
* **Part 4 (obstruction, audited; [research/wall1_new.md](research/wall1_new.md)).** In the iid
  plain-LWE embedding with `m = n = 512`, `q = 3329`, with probability `> 1 − 2^{−275}` every
  coordinate projection of dimension 2–400 (coordinates may be chosen after seeing `A, b`) is the full
  grid `Z^k`, which has no unique shortest pair. Coordinate-block routes (random orders, progressive
  deletion, best-of-many projections) and block-internal potentials therefore cannot work; adaptive
  BKZ prefix spans are not covered.
* **Part 5 (partial result, audited; [research/wall1_sublattice.md](research/wall1_sublattice.md)).**
  For Haar-random unimodular lattices, a simultaneous lower bound on `λ₁` of the projection onto the
  complement of **every** primitive prefix of covolume `≤ X` (Kim's flag mean-value theorem + Markov), so it
  holds for prefixes chosen adaptively by BKZ — immune to selection bias. Missing: a bound on the selected
  prefix's covolume, and the polynomial-`q` q-ary ensemble; at the GSA values the bound becomes vacuous as
  `n` grows.
* **Part 6 (audited; [research/wall1_prefix.md](research/wall1_prefix.md)).** Deterministic prefix-covolume
  envelope and a Schnorr-type ratio bound `g_t ≥ g_0 e^{−p_0^{(t)}}` for fully BKZ-β reduced bases (proven Hermite
  constants; both recursions are exact LP optima). With `g_0 ≥ λ1(L)` for Haar lattices, the 99% terminal height at
  `n = 700, β = 200` is only **9.22 bits below GSA**. The ratio bound is deterministic and holds for q-ary lattices too;
  the cost of producing a fully reduced basis and the projected planted law are not addressed.
* **Part 7 (audited negative result; [research/ratio_unique.md](research/ratio_unique.md)).** Rigorous: if every
  vector outside `ℤu` exceeds `R` and `‖u‖ ≤ R e^{−p_0^{(d−β)}}`, any fully BKZ-β reduced basis has `b_0 = ±u`. For the
  Kyber plain-LWE shapes the smallest certified `β` is `d` (701/1017/1351), i.e. exact full-dimensional SVP: the
  ratio bound gives no block-size saving, because the projected planted length is only bounded by `‖u‖`.
* **Part 8 (audited; [research/wall1_planted_flags.md](research/wall1_planted_flags.md)).** The flag criterion for
  terminal-block recovery must include the case `π_W(u) = a·v`, `a ≥ 2` (a shorter vector on the planted line's image);
  the corrected necessary-and-sufficient criterion is `a = 1` plus "every other line in `Q_W` is longer". Counterexamples:
  a fully reduced plain planted lattice with `a = 2` (outside the uSVP regime), and a reduced generic lattice where the
  unique shortest vector keeps its full length in the complement yet the terminal minimum is shorter. The probability of
  these events for random planted instances is open.
* **Part 9 (audited negative result; [research/wall1_planted_prob.md](research/wall1_planted_prob.md)).** At `β = 406` for the
  Kyber512 plain-LWE shapes (`m = 188, 511, 512`), for every `A` and every planting with coordinates `≤ 3`, some primitive prefix
  below the Part 6 cutoff violates the corrected criterion (witness `2b_k + u`, `a = 2`). So no all-prefix statement certifies
  `β = 406`; the failure probability for the prefix BKZ actually selects is open. For a fixed `W ⊂ L0`, `a = 1` and
  `‖π_W u‖²` concentrates (proved).
* **Part 10 (audited negative result; [research/wall1_selected.md](research/wall1_selected.md)).** Rotation equivariance gives
  an exact beta law for the projection of an *external* direction onto the complement of the selected prefix, but not for a
  short vector of the same lattice; choosing the prefix from the `u`-independent lattice `L0` gives exactly equal quotient
  covolumes, yet an explicit example has a projected horizontal vector shorter than the unique ambient shortest plant. Symmetry
  and independence alone cannot certify `β = 406`; what remains is the probability of a competing vector in the quotient that
  the actual algorithm selects.
* **Part 11 (audited; [research/wall1_markov_flags.md](research/wall1_markov_flags.md)).** Rerandomized tours are not a Markov
  chain on flags in general (two bases with the same prefix give disjoint next-prefix laws under the same unimodular update),
  and a symmetric irreducible walk on primitive lines has no stationary probability. A specific tour with a metric-dependent
  reduction step is not excluded.
* **Parts 12–14 (audited obstructions).** [wall1_gaussian_blocks.md](research/wall1_gaussian_blocks.md): with Gaussian block
  insertion the projected plant lies on the unique shortest line but with multiplicity `|b|`; as the width grows (smoothing error
  → 0) the probability of multiplicity one → 0. [wall1_duality.md](research/wall1_duality.md): exact dual criterion (primitive
  plant + strictly smallest marked hyperplane kernel), and two lattices with identical reversed dual blocks where the criterion
  holds in one and fails in the other — unmarked block statistics cannot certify recovery. [wall1_dynamics.md](research/wall1_dynamics.md):
  along an exact trajectory with a deterministic tie rule, the next block's law is not determined by its covolume (1/3 vs 1/2);
  random tie-breaking removes this discrepancy in the example.
* **Part 15 (audited; [research/wall1_fresh_samples.md](research/wall1_fresh_samples.md)).** A norm cutoff on the planted vector
  couples disjoint sample batches even with a fixed secret (two-sample example: 1/3 versus 1/2 or 0 after one observed bit);
  with errors fixed in advance the design coefficients stay independent. Open: whether a fresh batch represents the original
  projected block and keeps the planted line.
* **Part 16 (audited; [research/wall1_information.md](research/wall1_information.md)).** Uniform random tie-breaking does not
  restore covolume-only conditioning: a 4-dimensional binary kernel gives 2/5 vs 4/9 for two histories with the same terminal area.
  Transcript-length (entropy) bounds limit total leakage but a few bits can encode the next minimum itself; a concentration proof
  needs an information bound on that specific observable.
* **Part 17 (audited; [research/wall1_coupling.md](research/wall1_coupling.md)).** Replacing blocks by fresh Haar lattices has
  total variation error exactly 1 (rational vs atomless minima); path coupling and a discrete reference (exact for unexamined
  coordinate blocks) are proved. **Audit finding:** in the 4-dimensional example of Parts 16–17 the discrepancy disappears once
  one conditions on the full in-block Gram–Schmidt profile, so *profile-only* conditioning (rather than covolume-only) is still
  open and is the most promising lead.
* **Part 18 (audited; [research/wall1_smoothed.md](research/wall1_smoothed.md)).** Generic continuous metric noise makes
  reduction trajectories almost surely tie-free and locally stable, but an arbitrarily small anisotropic perturbation still gives
  conditional tail probabilities 1/3 vs 1/2 for two histories at almost every common covolume. Isotropic smoothing and
  profile-only conditioning remain open.
* **Part 19 (audited; [research/wall1_profile.md](research/wall1_profile.md)).** Given the history of selected lines, even the
  full Gram–Schmidt profile does not determine the next block's law, with uniform random tie-breaking: dimension 3 (revisits,
  same profile and current block, 4/5 vs 0; dimension-minimal) and dimension 5 (one forward sweep, 1/3 vs 2/5). Open: the
  process observed through successive scalar profiles only.
* Open, and the core of wall 1:
  * the law of the adaptively reduced prefix (after BKZ);
  * the projection bound for the planted vector;
  * the resulting provable block size and cost for Kyber.

## Wall 2: the sieve on BKZ-produced blocks (in progress)

* **Necessary condition for a smoothing invariant (new; [research/wall2.md](research/wall2.md)).**
  Take a determinant-one block of dimension `d` with a nonzero dual vector of length `1/T`. For
  every index-`p` sublattice, smoothing at width `R` after normalization requires
  `p ≥ ((T/R)·√(log(2/ε)/π))^d`. The dual vector survives every sublattice, and it and its
  negative alone contribute `2·exp(−πR²p^{2/d}/T²)` to the dual Gaussian mass. Skewed blocks
  therefore defeat every index cap based on dimension and determinant alone.
* Lean: `Wall2.dualPair_exceeds`, the scalar Gaussian inequality. The lattice argument and the
  index bound are on paper.
* **Fixed coordinate blocks are fine (new; [research/wall2b.md](research/wall2b.md)).** For a fixed
  coordinate block of dimension `d` in either i.i.d. `q`-ary ensemble, the normalized dual
  satisfies `Pr[λ₁(D) ≤ δ^{1/d}/3] ≤ δ`. At the Gaussian-heuristic radius the expected dual
  Gaussian mass is `e^{−Ω(d)}`, so index `p = 1` suffices w.h.p.: before BKZ, the obstruction above
  does not occur. A zero-plant example shows that unrestricted `q` can force a superpolynomial
  reciprocal dual minimum. Lean: `Wall2.incidenceTail` (finite incidence inequality); the
  applications are on paper.
* **Simultaneous statistics fail (audited; [research/wall2_simultaneous.md](research/wall2_simultaneous.md)).** For Haar
  lattices at `n = 700`, `b ∈ {100, 200, 400}`, the expected number of terminal prefixes below the GSA cutoff violating S1
  exceeds `2^{141599}` (mostly from the prefix count itself); interior blocks admit S1-violating continuations when the
  continuation determinant is unrestricted. A first-moment, all-blocks argument cannot certify the sieve on BKZ blocks.
* Open: blocks chosen adaptively by BKZ (this reduces to wall 1).

## A route around walls 1 and 2: the full-dimension sieve

Walls 1 and 2 only arise because the estimator's attacks call a sieve inside BKZ. Running the
average-case provable sieve on the planted LWE embedding lattice itself, with no BKZ, needs neither.
Choose the number of samples `m` to minimise the dimension `d = m + n + 1` subject to two
conditions:
* the stage-2 bound gives `λ₂ > R = 1.05·‖(e, s, 1)‖` except with probability `≤ 2^{−64}`;
* `R √(1 + B²) < q`.

Then the planted vector is the unique shortest vector and the sieve finds it (`python/full_dim_sieve.py`):

| Kyber (plain-LWE shape, `q = 3329`) | `d` | sieve `2^{0.2925 d}` (with P′) | T1 `2^{0.415 d}` | estimator | worst-case BKZ route |
| --- | --- | --- | --- | --- | --- |
| 512 | 688 | **201** | 286 | 143.8 | no admissible β |
| 768 | 1004 | **294** | 417 | 204.9 | no admissible β |
| 1024 | 1336 | **391** | 554 | 275.1 | no admissible β |

For Kyber512 the gap to the estimator is about 57 bits. The worst-case BKZ route gives no cost at all once `β ≤ d` is enforced. What
this route still needs:
1. **Static statistics S1, S2, S3′ for the planted embedding lattice at polynomial `q = 3329`**,
   with ratio `m/d ≈ 0.25`. T4b covers quasi-polynomial `q` and no planted vector: open, in
   progress.
2. Stage 2 (below): audit and Lean in progress.
3. The sieve: T1 is in Lean given the static hypotheses; `0.2925` uses P′ (paper) and the audited
   GFH theorem.
4. S5 initialization (`IdealUniformLeaves`). It is easier for `q`-ary lattices, since
   `qZ^d ⊂ Λ`.
5. The bit model.

**Obstruction found, and the repair to try ([research/planted_polyq.md](research/planted_polyq.md)).**
At the Kyber512 shape `(q, n, m, d) = (3329, 512, 175, 688)`, S1 fails for **every** `A`. The
terminal shell's squared-radius interval lies strictly inside `(4475, 4476)`, while every vector of
the embedding lattice has integer squared norm. So the shell is empty, and S3′ fails too. Lean:
`PolyQ.shell_empty_of_sq_gap` (the integer-spectrum obstruction; the endpoint inequalities were
checked by exact rational arithmetic outside Lean).

This is the `Z^n` obstruction again. The cause is the sieve's shell width `w = n^{−2}`, which is too
thin for integer lattices: the squared-radius width is about `0.02`. The note's §4 already says
integer lattices need width `Θ(1/n)`, giving a squared-radius width of about `13` at `d = 688`. That
in turn needs the algorithmic layer to tolerate constant-factor variation of lens volumes across a
shell (windows `[μ/C, Cμ]`). The Lean T1 (`prescribedScan_T1`) is stated for the thin shells, so it
must be redone for wide shells. In progress.

This does not replace walls 1 and 2: the estimator's cheaper BKZ-based attacks still have no
proof. It is the cheapest attack whose cost proof is within reach.

## Stage 2: the uSVP success condition with a planted vector (in progress)

* **`λ₂` lower bound, polynomial `q` (new; [research/usvp_planted.md](research/usvp_planted.md);
  audited: holds, [research/usvp_planted_audit.md](research/usvp_planted_audit.md);
  **proved in Lean: `Planted.badMatrices_probability`**).** For the plain-LWE embedding lattice
  (`d = m + n + 1`, planted `(e, s, 1)` with coordinates bounded by `B`), and with
  `G = (q^m / V_d)^{1/d}` the Gaussian-heuristic radius:
  `Pr_A[λ₂(L) ≤ R] ≤ ((R + √d/2)/G)^d` whenever `R √(1 + B²) < q`.
  * At `m = 2n`, bounded `B` and prime `q = Θ(n^a)` with `a > 3/2`, the failure probability is
    exponentially small at every fixed fraction of `G`.
  * Plain-LWE example of Kyber size: `q = 3329`, `m = 1024`, `n = 512`, `B = 3`, `R = 1000`
    (`G ≈ 2113`) gives failure probability `≈ 2^{−1616}`.
* Lean (`SigabaNeo.Planted`; axioms `propext`, `Classical.choice`, `Quot.sound`):
  * `badMatrices_probability`: for prime `q`, fixed `e, s` with `|coords| ≤ B`, `R ≥ 0` and
    `R √(1+B²) < q`, the uniform probability over `A` that the embedding lattice
    (`x + Ay ≡ t(As + e) mod q`) contains a nonzero `z` of norm `≤ R` that is not an integer
    multiple of `(e, s, 1)` is `≤ ((R + √d/2)/G)^d`;
  * `badMatrices_card` (probability `≤ #integer ball/q^m`) and `integerBall_card_le_volume`
    (`#integer ball ≤ V_d (R + √d/2)^d`, by disjoint unit cubes);
  * `planted_iff`: embedding membership is `A(y − ts) = te − x` over `F_q`;
  * `affineCount`: a feasible system has `q^{(n − rk X) m}` solutions;
  * `lift_multiple`: short points congruent to multiples of the planted vector are integer
    multiples.
* Open:
  * the success condition for windows chosen by BKZ from the same matrix (fixed windows have
    exact moments in the note);
  * full shell statistics at polynomial `q`;
  * Kyber's module structure.

## Direction of the GSA error (checked)

The estimator's CN11 simulator models the BKZ basis shape more closely than the GSA, including the
HKZ tail. It is still empirical. With it, the primal attacks on Kyber cost more than with the GSA:

| Kyber | uSVP GSA | uSVP CN11 | difference | BDD GSA | BDD CN11 | difference |
| --- | --- | --- | --- | --- | --- | --- |
| 512 | 143.8 | 146.8 | +3.0 | 140.2 | 142.1 | +1.9 |
| 768 | 204.9 | 209.9 | +5.0 | 201.0 | 203.9 | +3.0 |
| 1024 | 275.1 | 282.3 | +7.2 | 270.7 | 275.4 | +4.7 |

So the GSA errs in the attacker's favour here, which keeps `H` on the safe side. This is a
comparison of two models, not a proof.

## Stage 3: sieving (assumption (B))

The sieving cost `2^{0.292 β}` rests on three assumptions:

* **(A)** the Gaussian heuristic for lattice-point counts. For Haar-random lattices it is a
  theorem (Siegel, Rogers).
* **(B)** the list behaves like i.i.d. uniform points on a sphere. This is the open core.
* **(C)** BKZ's projected blocks behave like random lattices.

Research note: [research/provable_sieving.md](research/provable_sieving.md). Status:

* A claimed solution of (B) for Haar-random lattices: Doulgerakis–Laarhoven, arXiv:2609.37482
  (2026, not refereed). It solves exact SVP in `2^{0.2924n+o(n)}` time and `2^{0.2075n}` space. It
  rests on Laarhoven, arXiv:2609.13635 (quenched lattice statistics). Both are **claimed**, not
  verified here.
* The note proves the algorithmic layer on paper, given static hypotheses S1–S5 on a fixed
  lattice: exact uniformity of the lists, the acceptance rate, correctness in time `2^{0.415n}`.
  It also proves Lemma S3′ (SVP coverage from Rogers' formula at `k ≤ 3`) and the `q`-ary
  mean-value formula (Lemmas Q1, Q2).
* The deep input for exact SVP is gap **G1**: [Laa26] Proposition 5.1, quenched bounds on high
  moments of lens counts with every non-partition penalty below `3/4`. An adversarial audit
  ([research/g1_audit.md](research/g1_audit.md)) re-derived both bounds and found G1 **holds on
  the domain it states**, *given* the classical Rogers formula and spherical Gram density:
  * the feared two-free-parent relation `x₃ = x₁ + x₂ − d` has empty support, because the
    longitudinal constraint forces projection `≈ d/2`;
  * the worst surviving base is `e/4 < 3/4`;
  * the prefactor is `e^{O(h² log n)}`, a correction to the note, still `2^{o(n)}` at
    `h ≈ ln n`;
  * the endpoint bound excludes `α = 1`, which the SVP route does not use.

  [Laa26]'s Lean development assumes `ClassicalRogersFormula` and `ClassicalGramFormula`.
  **`ClassicalGramFormula` is now proved** for Lebesgue measure on every finite-dimensional real
  inner product space (`SigabaNeo.Rogers.Gram.classicalGramFormula_volume`,
  `Reduction/Rogers/ClassicalGram.lean`, from the spherical Gram law for every `s`,
  `spherical_gram_formula_all`; axioms `propext`, `Classical.choice`, `Quot.sound`). The archive
  statement was transcribed locally (`GramDensity.lean`); the archive itself was not rebuilt.
  `ClassicalRogersFormula` (Rogers' formula for Haar measure) remains open: Haar right invariance,
  a positive-mass arithmetic domain and the finite type-A diagonal integral are proved; the Siegel-set
  covering in general rank, the Haar bound on it, and the unfolding with the covolume factor remain.
* **`q`-ary lattices (the LWE side).** Here Lemma Q1 replaces Rogers' formula by linear algebra over
  `F_q`. Proved in Lean (`SigabaNeo.QAry`; axioms `propext`, `Classical.choice`, `Quot.sound`):

  | Theorem | Statement |
  | --- | --- |
  | `kernelCount`, `meanValue` | Lemma Q1: for uniform `A ∈ Z_q^{n×m}`, the average of a finite weighted tuple sum over `Λ_q^⊥(A)` is `Σ_x F(x)/q^{n·rk_{F_q}(x)}` |
  | `shortRank` | Lemma Q2: integer tuples with row norms `≤ R`, `R^k < q`, have equal ranks over `F_q` and `Q` |
  | `firstMoment` | Siegel analogue: a shell of nonzero integer vectors of radius `R < q` has expected count `|S|/q^n` |
  | `secondMoment`, `variance` | exact second moment and variance of shell counts for `R² < q` |

  Lemma Q3 (integer points in lens fibres, needed to compare the counts with volumes): proved on
  paper for separations in `[R/2, 3R/2]`, shell width `≍ 1/n`, `m ≥ n` and `R/m^{3/2} → ∞`
  ([research/qary.md](research/qary.md)). The general range and the higher-moment integrands are
  open, and the paper part is not in Lean. Modular coincidences at `m = 2n` are quantified there.
* **Reverse Minkowski dichotomy for (C) (new; negative;
  [research/reverse_minkowski_blocks.md](research/reverse_minkowski_blocks.md)).** The idea was
  that every block either has a dense sublattice (recurse into it) or is semistable, in which case
  reverse Minkowski bounds the counts. **It fails on both branches.**
  * A minimum-slope piece of the canonical filtration can miss every shortest vector.
  * Semistable lattices can exceed the S1 and S2 predictions by exponential factors.
  * Decisively, on `Z^n` squared norms are integers, so the sieve's thin terminal shell is
    **empty** in infinitely many dimensions, also after any fixed-prime-index re-randomization.
    The last transition then accepts nothing, which defeats T1 and the averaged route of
    Remark A′. Non-vacuous S2 counterexamples are given in dimensions 168 and 1542 (exact
    rational interval checks).
  * Lean: `RevMink.card_le_of_gaussian_mass`, a count bound from a Gaussian-mass bound. Axioms
    `propext`, `Classical.choice`, `Quot.sound`. The counterexamples are paper proofs.

  Conclusion: the shell-based provable sieve is inherently average-case. It cannot certify the
  sieve calls on arbitrary (worst-case) BKZ blocks. A growing, input-dependent re-randomization
  index remains unexplored.
* **The algorithmic layer in Lean (`SigabaNeo.Lattices.Sieve`).** The finite-shell sieve, for a
  fixed lattice given as finite shells, with the static hypotheses explicit. Axioms `propext`,
  `Classical.choice`, `Quot.sound` in all 17 checks:

  | Theorem | Statement |
  | --- | --- |
  | `exactCancellation`, `acceptance` | Lemma A: every target difference gets weight `b_min/(a_max |U|)`. The acceptance rate is exactly `(1+θ_T)/(12(1+θ_U))`, at least `99/1212` under S1. This corrects the note's `1/12`: the constant changes, the argument does not |
  | `bankFailure`, `mergeSurvival` | Lemma B: concentration gives a bad-bank bound; one merge survives with probability `≥ (1−δ)(1−ε)` |
  | `shellTree_uniform`, `survival_recurrence` | Theorem D: from i.i.d. uniform leaves, all output lists at a level have equal mass; the survival recurrence |
  | `terminalFailure_count`, `latticeScan_shortest` | Lemma F: under terminal coverage, S3′ and S4, every minimizer of the filtered scan is a shortest nonzero vector |
  | `scanBudget_le` | the exhaustive-scan comparison budget `≤ m·2^m·(2B²) + B²` |

  Added (`Reduction/Sieve/{Core,Bounds,Movers,Tree,Estimates}.lean`, same axioms):

  | Theorem | Statement |
  | --- | --- |
  | `scanBudget_prescribed` | for fixed `K`, all large `n` and depth `m ≤ K (log n)³`, the prescribed scan uses at most `(4/3)^n · e^{(2K+8) n/log n}` comparisons, i.e. `2^{0.415n + o(n)}` |
  | `bankFailure_explicit`, `moverChernoff`, `shellMerge_survival` | from S1 and S2, an explicit bad-bank bound `δ`; at a good bank, missing the `⌊M/16⌋` mover target has probability `≤ e^{−M/1000}` (Chernoff); one-merge survival `≥ (1−δ)(1−e^{−M/1000})` |
  | `prescribedScan_dimension` | under explicit geometric margins and coverage, the two-tree terminal scan finds a specified short vector with probability `≥ 1 − e^{−n/(2 log n)}` |
  | `idealUniformLeaves_factor` | the named hypothesis `IdealUniformLeaves` (the S5 sampler) gives the leaf product used by the recurrence |

  **T1 is complete in Lean, given the static hypotheses (`Sieve.prescribedScan_T1`).**
  * Statement: for fixed `K ≥ 0`, all large `n` and depth `m ≤ K (log n)³`, every lattice whose
    shells satisfy S1, S2, S3′ and S4, given ideal uniform leaves, has a shortest nonzero vector
    `v`. The exhaustive sieve hits `v` with probability `≥ 1 − e^{−n/(2 log n)}`, using
    `≤ (4/3)^n e^{(2K+8) n/log n}` comparisons, and every minimizer of a successful filtered scan
    is a shortest vector.
  * The lens margins (`prescribedLensMargins`, via a cylinder inside the lens:
    `lensVolume_relative`) and the terminal occupancy (`terminalOccupancy_eventually`) are proved.
  * Axioms `propext`, `Classical.choice`, `Quot.sound`.
  * Remaining assumptions: S1–S4, S3′ (about the lattice) and `IdealUniformLeaves` (the S5
    initialization sampler), all explicit premises.
* **`q`-ary sieving statistics (T4; new; [research/qary_sieving.md](research/qary_sieving.md)).**
  * **Paper proof (new).** For `Λ_q^⊥(A)` with lattice dimension `m`, `n = ⌊√m⌋` parity checks and a
    prime `q ∈ [e^{m^8}, 2⌈e^{m^8}⌉]`, the hypotheses S1, S2 and S3′ hold simultaneously with
    probability `1 − e^{−Ω(m)}` over `A`.
    * The proof moves the centered marked moments, up to order `O(log m)`, onto the Euclidean
      diagram sums with additive error `≤ e^{−m²}`. It then reuses the continuum diagram bounds of
      [Laa26] Prop 5.1 audited in g1_audit.md.
    * Lemma Q1 takes the place of Rogers' formula, so **no Haar measure and no Rogers formula
      are needed**. The remaining classical inputs are the spherical Gram density and the
      audited (not formalized) continuum diagram bounds.
    * With the algorithmic layer, this gives exact SVP on these lattices in time `(4/3)^{m+o(m)}`,
      or `(3/2)^{m/2+o(m)}` with Hypothesis P. The exponent is in the lattice dimension `m`.
  * Lean (`SigabaNeo.QAry`): `shortMeanValue`, `markedTail`. Axioms `propext`, `Classical.choice`,
    `Quot.sound`. The integration estimate and the sieve corollaries are paper proofs.
  * This first regime needs `n ≈ √m` and a doubly exponential `q`.
* **Toward cryptographic shapes (T4b; new; [research/qary_crypto_shapes.md](research/qary_crypto_shapes.md)).**
  * **Paper proof (new).** At **`m = 2n`**, and for every aspect ratio with `n/m` bounded away from 0
    and 1, S1, S2 and S3′ hold simultaneously with probability `1 − e^{−Ω(m)}`. This needs a
    **quasi-polynomial** prime `q ≍ exp(⌈log m⌉^6)`.
  * The new ingredient is a counting bound for modular coincidences. A tuple whose rational rank
    `t` drops to residue rank `u` is suppressed by `q^{−(t−u)(m−n)}`. Centering at the discrete
    fibre mean cancels the singleton terms exactly.
  * At fixed moment order, polynomial primes already suffice for the rank bound. The full sieve
    theorem still uses the quasi-polynomial prime.
  * Result: exact SVP on random `q`-ary lattices of these shapes in `(4/3)^{m+o(m)}` time w.h.p.,
    in the real-RAM model. The `(3/2)^{m/2+o(m)}` variant rested on Hypothesis P, which the audit
    found self-contradictory (below).
  * Lean: `QAry.meanValue_le_add_defect`, the finite mean-value transfer inequality with a
    rank-defect term. Axioms `propext`, `Classical.choice`, `Quot.sound`. The geometric counting
    bound and the corollaries are paper proofs.
  * **Audit ([research/t4_audit.md](research/t4_audit.md); independent, adversarial).**
    * T4 and T4b **hold** at the stated sieve radii, including `m = 2n`, given the classical Gram
      density and the Euclidean diagram estimates of the G1 audit. The exhaustive real-RAM bound
      `(4/3)^{m+o(m)}` follows.
    * Two overclaims fail. A transfer "at every positive radius" fails on the event `A = 0`.
      **Hypothesis P** (§3.9 of the note, behind every `(3/2)^{m/2}` / `2^{0.2925·}` time claim)
      **is self-contradictory as written**: at cosine `0.45`, P1 demands reporting with
      probability → 1 while P2 makes candidacy exponentially unlikely. The `0.2925` time bounds
      of the notes were therefore unverified until the repair below.
    * **Repair, Hypothesis P′ ([research/search_lemma.md](research/search_lemma.md); new).**
      Recall is required only at the query cosines the sieve actually uses. For arbitrary fixed
      indexed lists, Gao–Feng–Hu's product code with fresh rotations misses each required pair
      with probability `≤ e^{−Cn}`. With Lemmas H and I this gives real-RAM time
      `2^{(0.29248…+o(1))n}` and space `2^{(0.20751…+o(1))n}`.
      * [DL26]'s own `0.2924` claim is **not** affected: its Lemma 19(ii) asks for recall only on
        cosines in `[1/2 − 1/ℓ, 2/3]`.
      * Lean: `Search.transcriptMiss_le`, the finite-transcript union bound. The product-code
        construction and the running time are paper proofs.
      * P′ relies on [GFH26b] Theorem 4.2 / Proposition 4.3 (ePrint 2026/1844, not refereed).
        **Audit ([research/gfh_audit.md](research/gfh_audit.md)):** they support P′ for non-empty
        fixed lists in the real-RAM regime. Eq. (19) has a harmless empty-input defect, since P′
        returns immediately on empty lists. One shared Haar rotation per batch suffices.
        * Lean: `Search.productCodeMiss_le`, the conditional `m·q^B` miss bound. Axioms
          `propext`, `Classical.choice`, `Quot.sound`.
        * Checked on paper only: Haar concentration, wedge volumes, averaging over rotations,
          and traversal correctness and cost.
    * Priority: Kim–Kwon–Lee–Lee (ePrint 2026/2711) already prove exact SVP for random `q`-ary
      kernels in a different density regime. What may be new here is narrower: the
      shrinking-shell statistics at these radii. Even that is not confirmed.
  * **Lean (`SigabaNeo.Lattices.QAryMain`, partial; axioms `propext`, `Classical.choice`,
    `Quot.sound`).** No continuum or Gram-density hypothesis is used.

    | Theorem | Statement |
    | --- | --- |
    | `markedRawSum`, `markedCenteredSum` | exact raw and centered marked moments over all check matrices |
    | `markedDeviationUnion`, `staticFailure_le_rankSum` | Markov's inequality and a union bound over marks and levels: `P[S1, S2 or S3′ fails]` is at most an explicit finite sum of modular-rank terms, for the repository's sieve predicates |
    | `rankReplacement` | modular minus rational raw sums equals a sum over discrepant rank pairs with exact multiplicities |
    | `innerBallProbability` | for `1 ≤ R < q`, `P[Λ_q^⊥(A) meets the nonzero integer ball of radius R] ≤ #B/q^n` |

    Added (`QAry/MainCounting.lean`):
    * `projectedRankStratum` counts projected integer arrays with entries `≤ B`, rational rank `t`
      and residue rank `u`, with the factor `q^{−(t−u)m}`;
    * `centeredPartitionSum` proves the exact singleton cancellation.

    Added (`QAry/MainRowSpaces.lean`):
    * `rationalRowSpaceCount`: at most `(2B+1)^{kd}` rational row spaces of rank `d`;
    * `rationalRowPivots`: an injective coordinate projection on each such space;
    * `rationalRankStratumCount`, `modularRankStratumCount`: stratum counts, including pivots
      that lose rank mod `q`;
    * `freeingPivotError`: the error from dropping rational independence.

    Open in Lean, to reach `e^{−cm}` and the exact-SVP corollary:
    * identifying the partition arrays inside `rankMoment` and applying `centeredPartitionSum`;
    * summing the error over patterns;
    * the enlarged-window continuum estimates at the T4b radii.
  * **Still far from Kyber and LWE.** `q = 3329` is polynomial and far below `exp(log^6 m)`. LWE
    lattices contain a planted short vector. BKZ runs the sieve on projected blocks, which is
    assumption (C), refuted for worst-case blocks above. The bit model is open.
* **Re-randomization for (C) (new; [research/rerandomization.md](research/rerandomization.md)).**
  Replace a block `B` by a uniformly random index-`p` sublattice. A tuple whose residues span
  dimension `r` survives with probability `(p^{d−r} − 1)/(p^d − 1)`, which gives exact moments of
  every order for **every** input lattice.
  * Proved in Lean: `Rerand.meanValue` (the finite-support weighted identity, any arity) and
    `Rerand.nonzeroKernelCount`. Axioms: `propext`, `Classical.choice`, `Quot.sound`.
  * Paper proof only (not in Lean): **negative result**. For every `d ≥ 2` and prime `p` there are
    determinant-one lattices with HKZ-reduced bases, `diag(η, η⁻¹, 1, …)ℤ^d` with `η → 0`, for
    which every index-`p` sublattice violates the shell-count hypothesis S1. So
    re-randomization alone does not give the sieve's static hypotheses for arbitrary blocks.
    The obstruction is to S1, not to solvability: such blocks have `λ₁` far below the Gaussian
    heuristic. Treating "skewed" blocks separately is a possible next step.
* Open: (C) has no proof. BKZ's projected blocks are not Haar-random, and no analogue of
  Rogers' formula is known for them. So even a verified [DL26] would make sieving a theorem for
  random lattices, not for the sieve calls inside BKZ on LWE lattices.

## Stage 4 (planned): dual attacks

Following the Pouly–Shen line of rigorous dual-attack analyses.

The stage-1 numbers come from `python/proof_gap.py` (estimator `RC.MATZOV` costs, `python/lwemodel`).

## Dual attacks: list correlations (audited; [research/dual_list_correlation.md](research/dual_list_correlation.md))

For a complete shell under uniform input the off-diagonal score variance is exactly a (half-weighted) count of
modular collisions up to sign; for non-uniform input distinct, non-antipodal dual vectors can be perfectly
correlated (variance `N²`); sign flips and uniform subset selection do not remove correlations. Conditional guarantee:
mean gap `g` and variance sum `≤ g²/16` give advantage `≥ 3/4` for the midpoint test. Open: establishing these for
actual BKZ+sieve lists, and bridging fresh-input tests with Pouly–Shen's fixed-input Theorem 6.

## Dual attacks: MATZOV modulus switching and FFT (audited; [research/matzov_rigorous.md](research/matzov_rigorous.md))

Conditional extension of Pouly–Shen Theorem 6: with exact independent DGS draws, FFT over the rounded residues is exact and
recovery holds if the population gap exceeds `2(B + ε + d)` (rounding, numerical, sampling errors); guesses equal mod `p`
are indistinguishable, so lifts need separate handling. Not certified at the estimator's parameters. Estimator heuristics
listed (including an `Nf` bits/nats mix and the GJ21 independence heuristic in `fft_solver`); the estimator's secret entropy
exceeds the exact CBD entropy by 0.0062 / 0.0165 bits per coefficient.

## Dual attacks: tightening Pouly–Shen (audited; [research/pouly_shen_tight.md](research/pouly_shen_tight.md))

Union over candidate scores instead of `q^m`, a Banaszczyk-type tail and an explicit Hoeffding `N` lower the modeled cost at
the fixed Table 1 parameters by ≈ 0.50 / 1.67 / 0.02 bits (matched key coverage); the BKZ term (237.45 / 345.24 / 478.33)
is the floor. The dual gap to the estimator (≈ 88 bits for Kyber512) is essentially the BKZ/sieve part, i.e. walls 1–2.
