import Mathlib

theorem AdvancedEncryption.WE.QuadraticResidual.walsh_guards {I : Type} (s : Finset I) (q : I → Bool) :
    let sign := fun i => if q i then (-1 : ℤ) else 1
    let total := ∑ t ∈ s.powerset, ∏ i ∈ t, sign i
    ((∀ i ∈ s, q i = false) → total = (2 : ℤ) ^ s.card) ∧
    ((∃ i ∈ s, q i = true) → total = 0) := by
  sorry
