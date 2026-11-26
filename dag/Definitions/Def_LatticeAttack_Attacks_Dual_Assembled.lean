import Definitions.Def_LatticeAttack_Attacks_Dual_FreshMoments
import Definitions.Def_LatticeAttack_Attacks_Dual_CoordinateBounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

set_option autoImplicit true

/-!
# The rigorous dual distinguisher, assembled

`fresh_dual_test` takes the signed Fourier bias of the dual directions against the error as a
hypothesis. Here that bias is derived from two bounds, so the distinguisher depends only on
explicit, checkable conditions:

* every dual direction `w k` is the reduction of an integer vector of Euclidean norm `≤ W₀`;
* every error in the support of the error law is the reduction of an integer vector with all
  coordinates in `[−B, B]`.

Then, with `ε = 1 − (2π W₀ B √m / q)² / 2 > 0` and `N ≥ 8 log(1/δ)/ε²` fresh pairs, the threshold
test separates LWE samples from uniform ones with acceptance gap `≥ 1 − 2δ`
(`boundedDualTest`). The test computes `N` inner products of length `m`
(`dot_product_multiplications`).

The direction sampler is an input: producing short dual vectors is lattice reduction.
-/

open scoped Matrix
open MeasureTheory ProbabilityTheory

namespace SigabaNeo.DualMoments

variable {q m N : ℕ} [NeZero q]

/-- On integer lifts, the character is the cosine of the integer inner product. -/
theorem dotCharacter_cast_re (w e : Fin m → ℤ) :
    (dotCharacter (q := q) (fun j ↦ (w j : ZMod q)) (fun j ↦ (e j : ZMod q))).re =
      Real.cos (2 * Real.pi / q * ∑ j, (w j : ℝ) * e j) := by
  have hsum : (∑ j, (w j : ZMod q) * (e j : ZMod q)) = ((∑ j, w j * e j : ℤ) : ZMod q) := by
    push_cast; rfl
  change (ZMod.stdAddChar (∑ j, (w j : ZMod q) * (e j : ZMod q)) : ℂ).re = _
  rw [hsum, ZMod.stdAddChar_coe]
  have : (2 * ↑Real.pi * Complex.I * ((∑ j, w j * e j : ℤ) : ℂ) / (q : ℂ)) =
      ((2 * Real.pi / q * ∑ j, (w j : ℝ) * e j : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [this, Complex.exp_ofReal_mul_I_re]

/-- The signed bias of short dual directions against bounded errors. -/
theorem bounded_dual_bias {W : Type*} [Fintype W] [MeasurableSpace W] [MeasurableSingletonClass W]
    (w : W → Residues q m) (wl : W → Fin m → ℤ) (hwl : ∀ k, w k = fun j ↦ (wl k j : ZMod q))
    {W₀ B : ℝ} (hW : ∀ k, Real.sqrt (∑ j, ((wl k j : ℤ) : ℝ) ^ 2) ≤ W₀) (hB : 0 ≤ B)
    (D : Measure W) (E : Measure (Residues q m)) [IsProbabilityMeasure D] [IsProbabilityMeasure E]
    [MeasurableSingletonClass (Residues q m)]
    (hE : ∀ e, E.real {e} ≠ 0 → ∃ el : Fin m → ℤ, (∀ j, |((el j : ℤ) : ℝ)| ≤ B) ∧
      e = fun j ↦ (el j : ZMod q)) :
    1 - (2 * Real.pi / q * (W₀ * B * Real.sqrt m)) ^ 2 / 2 ≤
      ∫ k, ∫ e, (dotCharacter (w k) e).re ∂E ∂D := by
  set c := 1 - (2 * Real.pi / q * (W₀ * B * Real.sqrt m)) ^ 2 / 2
  have hq : (0 : ℝ) ≤ 2 * Real.pi / q := by positivity
  have hpt : ∀ k e, E.real {e} ≠ 0 → c ≤ (dotCharacter (w k) e).re := by
    intro k e he
    obtain ⟨el, hel, rfl⟩ := hE e he
    rw [hwl k, dotCharacter_cast_re]
    have hdot := abs_dot_le_of_coordinate_bound (fun j ↦ ((wl k j : ℤ) : ℝ))
      (fun j ↦ ((el j : ℤ) : ℝ)) (hW k) hB hel
    refine le_trans ?_ (Real.one_sub_sq_div_two_le_cos)
    have h1 : |2 * Real.pi / q * ∑ j, ((wl k j : ℤ) : ℝ) * el j| ≤
        2 * Real.pi / q * (W₀ * B * Real.sqrt m) := by
      rw [abs_mul, abs_of_nonneg hq]
      exact mul_le_mul_of_nonneg_left hdot hq
    have h2 := sq_le_sq' (neg_le_of_abs_le h1) (le_of_abs_le h1)
    simp only [c]
    linarith
  have hinner : ∀ k, c ≤ ∫ e, (dotCharacter (w k) e).re ∂E := by
    intro k
    rw [integral_fintype Integrable.of_finite]
    calc c = ∑ e, E.real {e} * c := by
            rw [← Finset.sum_mul, sum_measureReal_singleton, Finset.coe_univ, probReal_univ,
              one_mul]
      _ ≤ ∑ e, E.real {e} • (dotCharacter (w k) e).re := by
            apply Finset.sum_le_sum
            intro e _
            by_cases he : E.real {e} = 0
            · simp [he]
            · rw [smul_eq_mul]
              exact mul_le_mul_of_nonneg_left (hpt k e he) measureReal_nonneg
  calc c = ∫ _k, c ∂D := by simp
    _ ≤ _ := integral_mono (by fun_prop) Integrable.of_finite hinner

/-- **The dual distinguisher with bounded errors and short dual directions.** Fresh pairs of a
direction (from a sampler `D` of reductions of integer vectors of norm `≤ W₀` in the restricted
dual set) and a right-hand side; errors are reductions of integer vectors in `[−B, B]^m`. With
`ε = 1 − (2π W₀ B √m / q)²/2 > 0` and `N ≥ 8 log(1/δ)/ε²`, the threshold test `Σ cos ≥ Nε/2`
accepts LWE samples with probability at least `1 − 2δ` more than uniform ones. -/
theorem boundedDualTest {W : Type*} [Fintype W] [MeasurableSpace W] [MeasurableSingletonClass W]
    {n : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod q)) (s : Residues q n)
    (w : W → Residues q m) (hnz : ∀ k, w k ≠ 0) (hk : ∀ k, Matrix.vecMul (w k) A = 0)
    (wl : W → Fin m → ℤ) (hwl : ∀ k, w k = fun j ↦ (wl k j : ZMod q))
    {W₀ B : ℝ} (hW : ∀ k, Real.sqrt (∑ j, ((wl k j : ℤ) : ℝ) ^ 2) ≤ W₀) (hB : 0 ≤ B)
    (D : Measure W) (E U : Measure (Residues q m))
    [IsProbabilityMeasure D] [IsProbabilityMeasure E] [IsProbabilityMeasure U]
    [MeasurableSingletonClass (Residues q m)]
    (hE : ∀ e, E.real {e} ≠ 0 → ∃ el : Fin m → ℤ, (∀ j, |((el j : ℤ) : ℝ)| ≤ B) ∧
      e = fun j ↦ (el j : ZMod q))
    (hU : ∀ b, U.real {b} = (Fintype.card (Residues q m) : ℝ)⁻¹)
    {δ : ℝ} (hd : 0 < δ) (hn : 0 < N)
    (hε : 0 < 1 - (2 * Real.pi / q * (W₀ * B * Real.sqrt m)) ^ 2 / 2)
    (hs : 8 * Real.log (1 / δ) / (1 - (2 * Real.pi / q * (W₀ * B * Real.sqrt m)) ^ 2 / 2) ^ 2 ≤ N) :
    let ε := 1 - (2 * Real.pi / q * (W₀ * B * Real.sqrt m)) ^ 2 / 2
    let law := fun ν : Measure (Residues q m) ↦ Measure.pi (fun _ : Fin N ↦ D.prod ν)
    let accept := fun (offset : Residues q m) ↦
      {x : Fin N → W × Residues q m |
        N * ε / 2 ≤ ∑ i, (dotCharacter (w (x i).1) (offset + (x i).2)).re}
    1 - 2 * δ ≤ (law E).real (accept (A.mulVec s)) - (law U).real (accept 0) :=
  fresh_dual_test A s w hnz hk D E U hU hε hd hn hs
    (bounded_dual_bias w wl hwl hW hB D E hE)

end SigabaNeo.DualMoments

#print axioms SigabaNeo.DualMoments.dotCharacter_cast_re
#print axioms SigabaNeo.DualMoments.bounded_dual_bias
#print axioms SigabaNeo.DualMoments.boundedDualTest
