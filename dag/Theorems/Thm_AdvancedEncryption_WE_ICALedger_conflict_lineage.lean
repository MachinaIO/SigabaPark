import Mathlib

theorem AdvancedEncryption.WE.ICALedger.conflict_lineage {α : Type} (K : α → α → Prop) (T : ℕ → Set α) (monoT : Monotone T)
    (i j : ℕ) (hij : i ≤ j) (hit : ∃ a ∈ T i, ∃ b ∈ T i, K a b) :
    ∃ a ∈ T j, ∃ b ∈ T j, K a b := by
  sorry
