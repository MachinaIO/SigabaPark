import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Tactic

theorem solution {I : Type*} (s : Finset I) (w d c : I → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hc : ∀ i ∈ s, |c i| = 1) :
    ∑ i ∈ s, |w i * d i * c i| = ∑ i ∈ s, w i * |d i| := by
  apply Finset.sum_congr rfl
  intro i hi
  rw [abs_mul, abs_mul, abs_of_nonneg (hw i hi), hc i hi, mul_one]
