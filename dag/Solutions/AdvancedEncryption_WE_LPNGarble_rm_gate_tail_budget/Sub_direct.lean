import Mathlib

theorem solution (p : ℚ) (hp : 0 ≤ p) (hp' : p ≤ 1 / 6) :
    (2 : ℚ)^180 * (2 * 4096 * 47 * 2047) * (4 * p * (1-p))^256 ≤ 1 := by
  have ha : 0 ≤ 4 * p * (1-p) := by
    have h : 0 ≤ 1 - p := by linarith
    positivity
  have hb : 4 * p * (1-p) ≤ 9 / 16 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hp') (show 0 ≤ 5 / 6 - p by linarith)]
  have hc := pow_le_pow_left₀ ha hb 256
  calc
    (2 : ℚ)^180 * (2 * 4096 * 47 * 2047) * (4 * p * (1-p))^256 ≤
        2^180 * (2 * 4096 * 47 * 2047) * (9 / 16 : ℚ)^256 :=
      mul_le_mul_of_nonneg_left hc (by positivity)
    _ ≤ 1 := by norm_num
