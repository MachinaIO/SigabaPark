import Mathlib

theorem solution (p a b : ℝ) (hp : 0 ≤ p) :
    p*(a-b)^2/8 ≤ p*(a^2+b^2)/4 := by
  nlinarith [mul_nonneg hp (sq_nonneg (a+b))]
