import Definitions.Def_BucketLabel
open BucketLabel
theorem solution {I : Type} [Fintype I] (g cost : I → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (h : ∀ i, M * (g i)^2 ≤ cost i) :
    M * (∑ i, g i)^2 ≤ (Fintype.card I : ℝ) * ∑ i, cost i := by
  have a := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset I)) (f := g)
  simp only [Finset.card_univ] at a
  calc
    _ ≤ M*((Fintype.card I : ℝ)* ∑ i, (g i)^2) := mul_le_mul_of_nonneg_left a hM
    _ = (Fintype.card I : ℝ)* ∑ i, M*(g i)^2 := by rw [← Finset.mul_sum]; ring
    _ ≤ _ := by gcongr with i; exact h i
