import Mathlib.Tactic.Linarith

theorem AdvancedEncryption.WE.TwoInput.split3_frontier (m K1 K2 K3 E : ℕ) :
    (∃ a b c : ℕ, a + b + c = m ∧ a + K1 ≤ E ∧ b + K2 ≤ E ∧ c + K3 ≤ E) ↔
      m + K1 + K2 + K3 ≤ 3 * E ∧ K1 ≤ E ∧ K2 ≤ E ∧ K3 ≤ E := by
  sorry
