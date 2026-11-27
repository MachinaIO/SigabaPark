import Mathlib

theorem solution (b m : ℕ) (hm : 256 * b ≤ m)
    (hq : 128 ^ 3 * (8 * m + 4) ≤ 2 ^ b) :
    2 ^ 32 < 128 ^ 2 * (m - 1) * b := by
  have hten : 10 ≤ b := by
    by_contra! h
    have hsmall : (2 : ℕ) ^ b ≤ 2 ^ 9 := Nat.pow_le_pow_right (by decide) (by omega)
    norm_num at hsmall hq
    omega
  have hb : 33 ≤ b := by
    by_contra! h
    have hsmall : (2 : ℕ) ^ b ≤ 2 ^ 32 := Nat.pow_le_pow_right (by decide) (by omega)
    norm_num at hsmall hq
    omega
  have hm' : 8447 ≤ m - 1 := by omega
  calc
    2 ^ 32 < 128 ^ 2 * 8447 * 33 := by decide
    _ ≤ 128 ^ 2 * (m - 1) * b :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ hm') hb
