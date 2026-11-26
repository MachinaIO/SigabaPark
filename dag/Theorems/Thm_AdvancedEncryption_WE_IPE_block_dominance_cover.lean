import Lean

theorem AdvancedEncryption.WE.IPE.block_dominance_cover {I C : Type} {A : I → Type}
    (valid kept : (i : I) → A i → Prop) (hits : (i : I) → A i → C → Prop)
    (sound : ∀ i a, kept i a → valid i a)
    (dom : ∀ i a, valid i a → ∃ b, kept i b ∧ ∀ c, hits i a c → hits i b c) :
    (∃ x : (i : I) → A i, (∀ i, valid i (x i)) ∧ ∀ c, ∃ i, hits i (x i) c) ↔
    (∃ y : (i : I) → A i, (∀ i, kept i (y i)) ∧ ∀ c, ∃ i, hits i (y i) c) := by
  sorry
