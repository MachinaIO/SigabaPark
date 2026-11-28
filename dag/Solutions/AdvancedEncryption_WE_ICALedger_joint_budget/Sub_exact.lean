import Mathlib

theorem solution {I Ω : Type} [DecidableEq Ω] (targets : Finset I) (bad : I → Finset Ω) (m : ℕ)
    (h : ∀ i ∈ targets, (bad i).card ≤ m) :
    (targets.biUnion bad).card ≤ targets.card * m := by
  exact Finset.card_biUnion_le_card_mul _ _ _ h
