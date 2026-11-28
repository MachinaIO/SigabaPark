import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Tactic

theorem solution {I : Type*} (s : Finset I) (w v : I → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hv : ∀ i ∈ s, |v i| ≤ 1)
    (total : ∑ i ∈ s, w i = 1) :
    |∑ i ∈ s, w i * v i| ≤ 1 := by
  calc
    _ ≤ ∑ i ∈ s, |w i * v i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ s, w i := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul, abs_of_nonneg (hw i hi)]
      simpa using mul_le_mul_of_nonneg_left (hv i hi) (hw i hi)
    _ = _ := total
