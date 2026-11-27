import Mathlib
/-- Nearest scaled decoding is invariant under full ciphertext wraps. -/
theorem solution (p step x e wrap : ℤ) (hs : 0 < step)
    (lo : 0 ≤ e + step/2) (hi : e + step/2 < step) :
    ((step*x + e + (p*step)*wrap + step/2)/step) % p = x % p := by
  have h : step*x + e + p*step*wrap + step/2 =
      e + step/2 + (x+p*wrap)*step := by ring
  rw [h, Int.add_mul_ediv_right _ _ (by omega : step ≠ 0),
    Int.ediv_eq_zero_of_lt lo hi]
  simp [Int.add_emod, Int.mul_emod_right]
