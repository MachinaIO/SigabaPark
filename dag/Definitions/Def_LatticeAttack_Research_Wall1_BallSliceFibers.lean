import Definitions.Def_LatticeAttack_Research_Wall1_RawBallCount
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

set_option autoImplicit true

/-! Volumes of one- and two-dimensional open energy sections. -/
noncomputable section
namespace SigabaNeo.Wall1.RawBallRounding
open MeasureTheory Metric Set
open scoped ENNReal

/-- An open Euclidean section indexed by its squared radius. -/
def openEnergySection (k : ℕ) (t : ℝ) : Set (Fin k → ℝ) :=
  {y | ∑ i, (y i)^2 < t}

lemma measurableSet_openEnergySection (k : ℕ) (t : ℝ) :
    MeasurableSet (openEnergySection k t) := by
  exact measurableSet_lt (by fun_prop) measurable_const

lemma openEnergySection_eq_empty {k : ℕ} {t : ℝ} (ht : t ≤ 0) :
    openEnergySection k t = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro y hy
  have hh : 0 ≤ ∑ i, (y i)^2 := Finset.sum_nonneg fun i _ ↦ sq_nonneg _
  change (∑ i, (y i)^2) < t at hy
  linarith

lemma openEnergySection_eq_ball {k : ℕ} {t : ℝ} (ht : 0 ≤ t) :
    openEnergySection k t = WithLp.toLp 2 ⁻¹'
      ball (0 : EuclideanSpace ℝ (Fin k)) (Real.sqrt t) := by
  ext y
  change (∑ i, (y i)^2) < t ↔ dist (WithLp.toLp 2 y) 0 < Real.sqrt t
  rw [dist_zero_right]
  simpa only [EuclideanSpace.real_norm_sq_eq, Real.sq_sqrt ht] using
    (sq_lt_sq₀ (norm_nonneg (WithLp.toLp 2 y : EuclideanSpace ℝ (Fin k)))
      (Real.sqrt_nonneg t))

lemma volume_openEnergySection {k : ℕ} {t : ℝ} (ht : 0 ≤ t) :
    volume (openEnergySection k t) =
      volume (ball (0 : EuclideanSpace ℝ (Fin k)) (Real.sqrt t)) := by
  rw [openEnergySection_eq_ball ht]
  exact (PiLp.volume_preserving_toLp (Fin k)).measure_preimage
    measurableSet_ball.nullMeasurableSet

lemma volume_openEnergySection_ne_top (k : ℕ) (t : ℝ) :
    volume (openEnergySection k t) ≠ ⊤ := by
  by_cases ht : 0 ≤ t
  · rw [volume_openEnergySection ht]
    exact measure_ball_lt_top.ne
  · rw [openEnergySection_eq_empty (le_of_not_ge ht)]
    simp

lemma realVolume_openEnergySection_one (t : ℝ) :
    volume.real (openEnergySection 1 t) = 2 * Real.sqrt (max t 0) := by
  by_cases ht : 0 < t
  · rw [Measure.real, volume_openEnergySection ht.le]
    rw [InnerProductSpace.volume_ball_of_dim_odd (k := 0) (by simp)]
    simp [max_eq_left ht.le, ENNReal.toReal_mul, Real.sqrt_nonneg, mul_comm]
  · rw [openEnergySection_eq_empty (le_of_not_gt ht)]
    simp [max_eq_right (le_of_not_gt ht)]

lemma realVolume_openEnergySection_two (t : ℝ) :
    volume.real (openEnergySection 2 t) = Real.pi * max t 0 := by
  by_cases ht : 0 < t
  · rw [Measure.real, volume_openEnergySection ht.le, EuclideanSpace.volume_ball_fin_two]
    simp [max_eq_left ht.le, ENNReal.toReal_mul, Real.sqrt_nonneg,
      Real.sq_sqrt ht.le, Real.pi_nonneg, mul_comm]
  · rw [openEnergySection_eq_empty (le_of_not_gt ht)]
    simp [max_eq_right (le_of_not_gt ht)]

end SigabaNeo.Wall1.RawBallRounding
#print axioms SigabaNeo.Wall1.RawBallRounding.realVolume_openEnergySection_one
#print axioms SigabaNeo.Wall1.RawBallRounding.realVolume_openEnergySection_two
