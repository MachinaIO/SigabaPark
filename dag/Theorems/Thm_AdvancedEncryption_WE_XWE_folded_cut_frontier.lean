import Mathlib.Data.Nat.Basic

theorem AdvancedEncryption.WE.XWE.folded_cut_frontier (m j s e : ℕ) (hs : s ≤ e) :
    (∃ a u t : ℕ, a + u + t = m ∧ a ≤ e ∧ u ≤ j * (e - s) ∧ s + t ≤ 2 * e) ↔
      m + (j + 1) * s ≤ (j + 3) * e := by
  sorry
