import Mathlib

theorem solution (length : ℕ) : (∑ j ∈ Finset.range length, ((1:ℚ)/128)^j) ≤ 128/127 := by
  have h (n : ℕ) :
      (∑ j ∈ Finset.range n, ((1:ℚ)/128)^j) * (127/128) = 1-(1/128:ℚ)^n := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ,add_mul,ih,pow_succ]
      ring
  have hp := pow_nonneg (by norm_num : (0:ℚ) ≤ 1/128) length
  linarith [h length]
