import Definitions.Def_LatticeAttack_Research_Wall1_RawBallCount
import Definitions.Def_LatticeAttack_Research_Wall1_TwoCoordinateResidual
import Mathlib.Algebra.Order.Round
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
set_option autoImplicit true

/-! # Planar integer-disk lower bound

Nearest-integer rounding covers the inner disk by unit squares centered at
admissible lattice points. The energy interpretation requires nonnegative
squared radius; `closedLifts 2 (sqrt y)` contains zero even when `y < 0`.
-/

noncomputable section
open MeasureTheory Metric Set Real
open scoped BigOperators ENNReal
namespace SigabaNeo.Wall1.RawBallRounding

theorem planar_closedLifts_lower (R : ℝ) (hR : 0 ≤ R) :
    Real.pi * (max (R - 1 / Real.sqrt 2) 0)^2 ≤ (closedLifts 2 R).card := by
  classical
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hs2 : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
  have hc : Real.sqrt 2 / 2 = 1 / Real.sqrt 2 := by
    apply (eq_div_iff (ne_of_gt hs)).2
    nlinarith
  by_cases hsmall : R ≤ 1 / Real.sqrt 2
  · rw [max_eq_right (sub_nonpos.2 hsmall)]
    simp
  have hr : 0 ≤ R - 1 / Real.sqrt 2 := by linarith
  rw [max_eq_left hr]
  let T := closedLifts 2 R
  let cube (z : Fin 2 → ℤ) := univ.pi (fun i ↦ Icc ((z i : ℝ)-1/2) ((z i : ℝ)+1/2))
  have vol z : volume (cube z) = 1 := by
    dsimp [cube]
    rw [volume_pi_pi]
    norm_num [Real.volume_Icc]
  let r := R - 1 / Real.sqrt 2
  let D := closedBall (0 : EuclideanSpace ℝ (Fin 2)) r
  have incl : WithLp.toLp 2 ⁻¹' D ⊆ (⋃ z ∈ T, cube z) := by
    intro x hx
    let z : Fin 2 → ℤ := fun i ↦ round (x i)
    let v : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 (fun i ↦ (z i : ℝ))
    let y : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 x
    have hy : ‖y‖ ≤ r := by
      change dist y 0 ≤ r at hx
      simpa only [dist_zero_right] using hx
    have hd : ‖v-y‖ ≤ Real.sqrt 2 / 2 := by
      apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
      rw [EuclideanSpace.real_norm_sq_eq, div_pow, hs2]
      calc
        _ ≤ ∑ _ : Fin 2, (1/2 : ℝ)^2 := by
          apply Finset.sum_le_sum
          intro i _
          have hi := abs_sub_round (x i)
          change ((z i : ℝ) - x i)^2 ≤ _
          rw [sub_sq_comm]
          simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1/2)).2 hi
        _ = _ := by norm_num
    have hv : ‖v‖ ≤ R := by
      have hh := norm_le_norm_sub_add v y
      rw [hc] at hd
      dsimp [r] at hy
      linarith
    have hz : z ∈ T := by
      apply (mem_closedLifts hR z).2
      have hh := (sq_le_sq₀ (norm_nonneg v) hR).2 hv
      simpa [EuclideanSpace.real_norm_sq_eq, v, energy] using hh
    apply mem_iUnion₂.mpr ⟨z,hz,?_⟩
    intro i _
    have hi := abs_le.mp (abs_sub_round (x i))
    change (z i : ℝ)-1/2 ≤ x i ∧ x i ≤ (z i : ℝ)+1/2
    dsimp [z]
    constructor <;> linarith [hi.1,hi.2]
  have hvol := (measure_mono (μ := volume) incl).trans (measure_biUnion_finset_le T cube)
  rw [(PiLp.volume_preserving_toLp (Fin 2)).measure_preimage measurableSet_closedBall.nullMeasurableSet] at hvol
  simp only [vol, Finset.sum_const, nsmul_eq_mul, mul_one] at hvol
  have hh := ENNReal.toReal_mono (by simp : (T.card : ℝ≥0∞) ≠ ⊤) hvol
  have hr' : 0 ≤ r := hr
  rw [EuclideanSpace.volume_closedBall_fin_two] at hh
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal hr', ENNReal.toReal_ofReal Real.pi_nonneg,
    ENNReal.toReal_natCast, mul_comm] using hh


/-- Energy-parameter version of the planar nearest-rounding lower bound. -/
theorem planar_closedLifts_sqrt_lower (y : ℝ) :
    Real.pi * (max (Real.sqrt y - 1 / Real.sqrt 2) 0)^2 ≤
      (closedLifts 2 (Real.sqrt y)).card :=
  planar_closedLifts_lower (Real.sqrt y) (Real.sqrt_nonneg y)

lemma mem_planar_closedLifts_sqrt {y : ℝ} (hy : 0 ≤ y) (z : Fin 2 → ℤ) :
    z ∈ closedLifts 2 (Real.sqrt y) ↔ ∑ i, (z i : ℝ)^2 ≤ y := by
  rw [mem_closedLifts (Real.sqrt_nonneg y), Real.sq_sqrt hy]
  rfl

/-- Unlike a square-root ball, this set is empty for negative available energy. -/
def planarCompletions (y : ℝ) : Finset (Fin 2 → ℤ) :=
  if 0 ≤ y then closedLifts 2 (Real.sqrt y) else ∅

theorem mem_planarCompletions (y : ℝ) (z : Fin 2 → ℤ) :
    z ∈ planarCompletions y ↔ energy z ≤ y := by
  by_cases hy : 0 ≤ y
  · simpa only [planarCompletions, if_pos hy, energy] using mem_planar_closedLifts_sqrt hy z
  · have he : 0 ≤ energy z := Finset.sum_nonneg fun i _ ↦ sq_nonneg _
    have hn : ¬ energy z ≤ y := by linarith
    simp [planarCompletions, hy, hn]

theorem planarCompletions_lower (y : ℝ) :
    Real.pi * TwoCoordinateResidual.residual (1 / Real.sqrt 2) y ≤
      (planarCompletions y).card := by
  by_cases hy : 0 ≤ y
  · simpa only [planarCompletions, if_pos hy, TwoCoordinateResidual.residual] using
      planar_closedLifts_sqrt_lower y
  · have hc : 0 ≤ 1 / Real.sqrt 2 := by positivity
    simp [planarCompletions, hy, TwoCoordinateResidual.residual,
      Real.sqrt_eq_zero_of_nonpos (le_of_not_ge hy)]

#print axioms mem_planarCompletions
#print axioms planarCompletions_lower

#print axioms planar_closedLifts_sqrt_lower
#print axioms mem_planar_closedLifts_sqrt

#print axioms planar_closedLifts_lower
end SigabaNeo.Wall1.RawBallRounding
