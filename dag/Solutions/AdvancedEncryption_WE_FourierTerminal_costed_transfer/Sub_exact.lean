import Mathlib

theorem solution (gap keep win original wrapper evaluator : ℝ) (k h : ℕ)
    (hk : 0 < keep) (recovers : keep * gap^2 ≤ win)
    (hard : (2:ℝ)^h * win ≤ 2*evaluator + 1058 + wrapper)
    (budget : (2:ℝ)^k * (2*evaluator + 1058 + wrapper) ≤ (2:ℝ)^h * keep * original) :
    (2:ℝ)^k * gap^2 ≤ original := by
  have st := (mul_le_mul_of_nonneg_left recovers (by positivity : (0:ℝ) ≤ 2^h)).trans hard
  have sc := (mul_le_mul_of_nonneg_left st (by positivity : (0:ℝ) ≤ 2^k)).trans budget
  apply le_of_mul_le_mul_left (a := (2:ℝ)^h * keep) _ (by positivity)
  calc
    (2:ℝ)^h * keep * ((2:ℝ)^k * gap^2) = (2:ℝ)^k * ((2:ℝ)^h * (keep * gap^2)) := by ring
    _ ≤ _ := sc
