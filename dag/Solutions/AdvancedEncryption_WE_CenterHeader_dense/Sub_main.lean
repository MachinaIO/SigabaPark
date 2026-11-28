import Definitions.Def_AffineCenterHeader

open AffineCenterHeader

set_option exponentiation.threshold 1024

theorem solution (m q L : Nat) (hl : 1 ≤ L)
    (hm : 64 * L^2 ≤ m) (hq : 8*m^2 ≤ q) (hb : q < 2^(L+1)) :
    2^32 < m^2 := by
  have step (k : Nat) (h : k ≤ L) : 8*(64*k^2)^2 < 2^(L+1) := by
    have hm' : 64*k^2 ≤ m := Nat.le_trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h 2)) hm
    exact Nat.lt_of_le_of_lt (Nat.le_trans (Nat.mul_le_mul_left 8 (Nat.pow_le_pow_left hm' 2)) hq) hb
  have grow (p a : Nat) (bound : a < 2^(L+1)) (lo : 2^p ≤ a) : p ≤ L := by
    by_cases h : p ≤ L
    · exact h
    have e : L+1 ≤ p := by omega
    have := Nat.pow_le_pow_right (by decide : 0 < 2) e
    omega
  have h15 := grow 15 _ (step 1 hl) (by decide)
  have h30 := grow 30 _ (step 15 h15) (by decide)
  have h34 := grow 34 _ (step 30 h30) (by decide)
  have hmin : 73984 ≤ m := Nat.le_trans (Nat.mul_le_mul_left 64 (Nat.pow_le_pow_left h34 2)) hm
  exact Nat.lt_of_lt_of_le (by decide : 2^32 < 73984^2) (Nat.pow_le_pow_left hmin 2)
