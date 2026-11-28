import Mathlib

open scoped BigOperators

theorem solution {I : Type} [Fintype I] (c e : I → ℤ) (delta W B : ℤ)
    (hd : |delta| ≤ B) (hw : ∀ i, |e i| ≤ W) :
    |delta - ∑ i, c i * e i| ≤ B + (∑ i, |c i|) * W := by
  calc
    _ ≤ |delta| + |∑ i, c i * e i| := abs_sub _ _
    _ ≤ B + ∑ i, |c i * e i| := add_le_add hd (Finset.abs_sum_le_sum_abs _ _)
    _ ≤ B + ∑ i, |c i| * W := by
      gcongr with i
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hw i) (abs_nonneg _)
    _ = _ := by rw [Finset.sum_mul]
