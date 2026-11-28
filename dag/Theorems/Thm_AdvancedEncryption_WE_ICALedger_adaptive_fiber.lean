import Mathlib

theorem AdvancedEncryption.WE.ICALedger.adaptive_fiber {H : Type} [Fintype H] (ell arity : ℕ) (t : H → (Fin arity → Fin (2^ell))) :
    Fintype.card {p : H × (Fin arity → Fin (2^ell)) // p.2 = t p.1} = Fintype.card H ∧
    Fintype.card (H × (Fin arity → Fin (2^ell))) = Fintype.card H * (2^ell)^arity := by
  sorry
