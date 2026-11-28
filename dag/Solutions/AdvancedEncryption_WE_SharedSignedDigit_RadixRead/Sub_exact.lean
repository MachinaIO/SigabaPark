import Mathlib

theorem solution (rest h : ℕ) (b : Bool) (hh : 0 < h) (hle : h < 4) :
    ((4 * rest + (if b then h else 0)) % 4 ≠ 0) ↔ b = true := by
  cases b <;> simp_all [Nat.add_mod, Nat.mod_eq_of_lt] <;> omega
