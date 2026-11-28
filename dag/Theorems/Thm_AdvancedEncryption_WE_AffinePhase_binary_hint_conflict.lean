import Mathlib

theorem AdvancedEncryption.WE.AffinePhase.binary_hint_conflict (f : ℤ → Bool) (h : ℕ) :
    ∃ z : ℤ, f z = f (z+h) ∨ f z = f (z+h+1) := by sorry
