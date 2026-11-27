import Mathlib

theorem solution (b : ℕ)
    (fits : 516 * (4099 * 2^b - 1) < (2:ℕ)^32) : b ≤ 10 := by
  by_contra! hh
  have p : (2:ℕ)^11 ≤ 2^b := Nat.pow_le_pow_right (by decide) hh
  norm_num at p fits
  omega
