import Mathlib

theorem solution (t p x : ℤ) (hl : -32768 ≤ x) (hu : x ≤ 32768) :
    ((2*t) % (2*p)) / 2 = t % p ∧
    (if x % 65537 ≤ 32768 then x % 65537 else x % 65537 - 65537) = x := by
  constructor
  · rw [Int.mul_emod_mul_of_pos t p (by decide : (0:ℤ)<2)]
    exact Int.mul_ediv_cancel_left _ (by decide : (2:ℤ) ≠ 0)
  · split_ifs <;> omega
