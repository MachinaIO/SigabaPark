import Mathlib.Tactic

theorem solution (n d t : Nat) (w : Nat) (_hw : w ≤ 2 ^ n)
    (hd : 2 ^ n ≤ w * 2 ^ d)
    (ht : (2 ^ d - 1) ^ t * 2 ^ 127 ≤ (2 ^ d) ^ t) :
    (2 ^ n - w) ^ t * 2 ^ 127 ≤ (2 ^ n) ^ t := by
  have hq : 0 < 2^d := by positivity
  have hstep : (2^n - w) * 2^d ≤ (2^n) * (2^d - 1) := by
    rw [Nat.sub_mul, Nat.mul_sub, Nat.mul_one]
    omega
  have hp := Nat.pow_le_pow_left hstep t
  rw [Nat.mul_pow, Nat.mul_pow] at hp
  have h1 := Nat.mul_le_mul_right (2^127) hp
  have h2 := Nat.mul_le_mul_left ((2^n)^t) ht
  have H : (2^n-w)^t * 2^127 * (2^d)^t ≤ (2^n)^t * (2^d)^t := by
    calc
      _ = ((2^n-w)^t * (2^d)^t) * 2^127 := by ring
      _ ≤ _ := h1
      _ = (2^n)^t * ((2^d-1)^t * 2^127) := by ring
      _ ≤ _ := h2
  exact Nat.le_of_mul_le_mul_right H (by positivity)
