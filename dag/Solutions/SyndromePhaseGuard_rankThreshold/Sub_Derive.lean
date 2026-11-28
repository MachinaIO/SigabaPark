import Mathlib.Tactic

theorem solution (r : ℕ) (t : ℝ) (h : 1 / 2 ≤ t)
    (hmoment : t ^ 2 * (2 : ℝ) ^ r ≤ 2) : r ≤ 3 := by
  by_contra! hr
  have hp : (2 : ℝ) ^ 4 ≤ 2 ^ r := pow_le_pow_right₀ (by norm_num) (by omega)
  norm_num at hp
  have hs : (1 : ℝ) / 4 ≤ t ^ 2 := by nlinarith [sq_nonneg (t - 1 / 2)]
  nlinarith [mul_le_mul_of_nonneg_right hs (by positivity : 0 ≤ (2 : ℝ) ^ r)]
