import Mathlib

theorem solution {F : Type} [Field F] (τ m c : F) (d : ℕ) :
    c + (m - (m - τ))^d = c + τ^d := by
  rw [sub_sub_cancel]
