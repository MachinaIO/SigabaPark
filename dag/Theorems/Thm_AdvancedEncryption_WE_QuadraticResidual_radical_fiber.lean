import Mathlib

theorem AdvancedEncryption.WE.QuadraticResidual.radical_fiber {H G : Type} [AddCommGroup H] [AddCommGroup G] (D : H →+ G) (b : G) :
    ((∃ r, b + D r = 0) ↔ -b ∈ Set.range D) ∧
    ∀ r : H, b + D r = 0 → Nonempty ({s : H // b + D s = 0} ≃ D.ker) := by
  sorry
