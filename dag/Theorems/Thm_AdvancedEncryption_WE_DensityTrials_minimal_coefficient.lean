import Mathlib

open scoped BigOperators

theorem AdvancedEncryption.WE.DensityTrials.minimal_coefficient {I G : Type} [DecidableEq I] [AddCommGroup G]
    (O : AddSubgroup G) (c : Finset I → G) (s : Finset I)
    (hproper : ∀ t, t ⊂ s → c t ∈ O) :
    (∑ t ∈ s.powerset, c t) ∈ O ↔ c s ∈ O := by sorry
