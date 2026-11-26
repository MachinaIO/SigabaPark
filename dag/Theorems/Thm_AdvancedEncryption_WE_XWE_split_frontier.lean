import Mathlib

theorem AdvancedEncryption.WE.XWE.split_frontier (n e d h : ℕ) :
    (∃ a b c : ℕ, a + b + c = n ∧ max (a + c) b ≤ e ∧ max (max a b) c ≤ d ∧ b ≤ h) ↔
      n ≤ 2 * e ∧ n ≤ e + d ∧ n ≤ 3 * d ∧ n ≤ h + e ∧ n ≤ h + 2 * d := by
  sorry
