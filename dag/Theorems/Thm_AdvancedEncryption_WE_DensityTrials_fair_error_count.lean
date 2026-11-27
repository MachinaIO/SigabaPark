import Mathlib

theorem AdvancedEncryption.WE.DensityTrials.fair_error_count {W : Type} [Fintype W] (ok : W → Bool) (t : Nat) (m : Bool) :
    Nat.card {p : (Fin t → W) × Bool //
      (∀ i, ok (p.1 i) = false) ∧ p.2 ≠ m} =
      Nat.card {x : W // ok x = false} ^ t := by sorry
