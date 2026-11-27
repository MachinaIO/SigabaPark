import Mathlib

theorem solution (s q : ℕ)
    (hclock : q < 2 ^ 32)
    (hcorrect : (2 ^ 127 - 1) * 2 ^ s ≤ 2 ^ 127 * q) : s ≤ 31 := by
  by_contra! hs
  have hpow : (2 : ℕ) ^ 32 ≤ 2 ^ s := Nat.pow_le_pow_right (by decide) hs
  norm_num at hclock hcorrect hpow
  omega
