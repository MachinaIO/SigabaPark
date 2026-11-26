import Mathlib.Data.Nat.Basic

theorem AdvancedEncryption.WE.XWE.folded_cut_asymmetric (m j s e k h : ℕ) (hs : s ≤ e) (hk : s ≤ k) :
    (∃ first middle left right : ℕ,
      first + middle + left + right = m ∧ first ≤ e ∧ middle ≤ j * (e-s) ∧
      s + left ≤ k ∧ right ≤ h) ↔ m + (j+1)*s ≤ (j+1)*e + k + h := by
  sorry
