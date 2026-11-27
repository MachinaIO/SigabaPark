import Mathlib

theorem AdvancedEncryption.WE.Dataset.certificate_fibers {W R V P : Type*} (accept : W → Prop) (view : R → V)
    (cert : V → W → P) (key : R → Bool) :
    (∃ readKey : V → W → P → Bool,
      ∀ r w, accept w → readKey (view r) w (cert (view r) w) = key r) ↔
    (∀ r s, view r = view s → (∃ w, accept w) → key r = key s) := by
  sorry
