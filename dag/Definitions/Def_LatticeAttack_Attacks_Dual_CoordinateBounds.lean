import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit true

namespace SigabaNeo.DualMoments

/-- A coordinate box controls every real linear form of bounded Euclidean norm. -/
theorem abs_dot_le_of_coordinate_bound {m : ℕ} (w e : Fin m → ℝ) {W B : ℝ}
    (hw : Real.sqrt (∑ i, w i ^ 2) ≤ W) (hB : 0 ≤ B) (he : ∀ i, |e i| ≤ B) :
    |∑ i, w i * e i| ≤ W * B * Real.sqrt m := by
  have hl : ∑ i, |w i| ≤ Real.sqrt (∑ i, w i ^ 2) * Real.sqrt m := by
    simpa using Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun i ↦ |w i|) (fun _ ↦ 1)
  calc
    _ ≤ ∑ i, |w i * e i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |w i| * B := Finset.sum_le_sum fun i _ ↦ by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (he i) (abs_nonneg _)
    _ = (∑ i, |w i|) * B := (Finset.sum_mul ..).symm
    _ ≤ (W * Real.sqrt m) * B := by
      gcongr
      exact hl.trans (mul_le_mul_of_nonneg_right hw (Real.sqrt_nonneg _))
    _ = _ := by ring

/-- Two-sided integer Gaussian tail beyond a positive integer cutoff. The normalizer
is at least one because the weight at zero is one. -/
theorem discreteGaussian_tail {a Z : ℝ} (ha : 0 < a) (hZ : 1 ≤ Z) {T : ℕ} (hT : 0 < T) :
    2 * (∑' k : ℕ, Real.exp (-a * ((T : ℝ) + k) ^ 2)) / Z ≤
      2 * Real.exp (-a * (T : ℝ) ^ 2) / (1 - Real.exp (-a)) := by
  have hr : Real.exp (-a) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hs := (summable_geometric_of_lt_one (Real.exp_pos (-a)).le hr).mul_left
    (Real.exp (-a * (T : ℝ) ^ 2))
  have h : ∀ k : ℕ, Real.exp (-a * ((T : ℝ) + k) ^ 2) ≤
      Real.exp (-a * (T : ℝ) ^ 2) * Real.exp (-a) ^ k := by
    intro k
    rw [← Real.exp_nat_mul, ← Real.exp_add, Real.exp_le_exp]
    have ht : (1 : ℝ) ≤ T := by exact_mod_cast hT
    have hk : (0 : ℝ) ≤ k := by positivity
    nlinarith [mul_nonneg ha.le (mul_nonneg (sub_nonneg.mpr ht) hk),
      mul_nonneg ha.le (sq_nonneg (k : ℝ)), mul_nonneg ha.le hk]
  have hb := (Summable.of_nonneg_of_le (fun k ↦ (Real.exp_pos _).le) h hs).tsum_le_tsum h hs
  rw [tsum_mul_left, tsum_geometric_of_lt_one (Real.exp_pos _).le hr] at hb
  calc
    _ ≤ 2 * (∑' k : ℕ, Real.exp (-a * ((T : ℝ) + k) ^ 2)) :=
      div_le_self (by positivity) hZ
    _ ≤ _ := by rw [div_eq_mul_inv]; linarith

#print axioms abs_dot_le_of_coordinate_bound
#print axioms discreteGaussian_tail

end SigabaNeo.DualMoments
