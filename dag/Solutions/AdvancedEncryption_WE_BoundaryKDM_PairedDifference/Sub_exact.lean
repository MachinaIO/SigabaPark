import Mathlib

theorem solution {I : Type*} [Fintype I] (weight val : I → ℝ) :
    (∑ i, ∑ j, (weight i * val i) * (weight j * val j)) =
    (∑ i, weight i * val i)^2 := by
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul, pow_two]
