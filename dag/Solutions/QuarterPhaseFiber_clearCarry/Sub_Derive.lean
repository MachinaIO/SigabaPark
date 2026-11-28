import Mathlib.Tactic

theorem solution (n h p : ℕ) :
    ((n + 2 * (n / 2 % 2 + h + p)) % 4) / 2 = (h + p) % 2 := by
  omega
