import Mathlib.Data.List.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

theorem AdvancedEncryption.WE.KSplit.chain_frontier (m j s e : ℕ) :
    (∃ a c : ℕ, ∃ L : List ℕ, L.length = j ∧ a + L.sum + c = m ∧ a ≤ e ∧ c ≤ e ∧
        ∀ x ∈ L, x + s ≤ e) ↔
      m + j * s ≤ (j + 2) * e ∧ (j = 0 ∨ s ≤ e) := by
  sorry
