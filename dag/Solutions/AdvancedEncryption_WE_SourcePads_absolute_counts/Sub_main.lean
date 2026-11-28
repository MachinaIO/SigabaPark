import Mathlib

open scoped BigOperators

theorem solution {I : Type} [Fintype I] (d : I → ℝ) (bound : ℝ)
    (h : (∑ i, (d i)^2) ≤ bound) :
    (∑ i, |d i|)^2 ≤ (Fintype.card I : ℝ)*bound := by
  calc
    _ ≤ (Fintype.card I : ℝ)*∑ i, |d i|^2 := by
      simpa using (sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i => |d i|))
    _ ≤ _ := by simpa using mul_le_mul_of_nonneg_left h (by positivity : (0:ℝ) ≤ Fintype.card I)
