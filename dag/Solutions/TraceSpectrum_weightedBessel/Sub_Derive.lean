import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Tactic

theorem solution {E I : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x : E) (s : Finset I) (v : I → E) (h : Orthonormal ℝ v)
    (a : I → ℝ) (ha : ∀ i ∈ s, |a i| ≤ ‖inner ℝ (v i) x‖) :
    ∑ i ∈ s, (a i)^2 ≤ ‖x‖^2 := by
  calc
    ∑ i ∈ s, (a i)^2 ≤ ∑ i ∈ s, ‖inner ℝ (v i) x‖^2 := by
      apply Finset.sum_le_sum
      intro i hi
      have hab := ha i hi
      nlinarith [sq_abs (a i), abs_nonneg (a i), norm_nonneg (inner ℝ (v i) x)]
    _ ≤ _ := h.sum_inner_products_le x
