import Mathlib

theorem AdvancedEncryption.WE.Separator.support_insert {α : Type*} [DecidableEq α]
    (s : Finset (Finset α)) (u live : Finset α) :
    (∃ t ∈ (if ∃ v ∈ s, v ⊆ u then s else insert u (s.filter (fun v => ¬u ⊆ v))), t ⊆ live) ↔
      u ⊆ live ∨ ∃ t ∈ s, t ⊆ live := by sorry
