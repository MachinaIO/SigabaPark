import Mathlib

theorem AdvancedEncryption.WE.JoinRoute.overlap_coefficient {T : Type} [DecidableEq T] (P Q : Finset T) :
    (∑ i ∈ P, ∑ j ∈ Q, if i = j then (1:ℕ) else 0) = (P ∩ Q).card := by
  sorry
