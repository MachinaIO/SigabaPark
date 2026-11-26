import SigabaNeoStd

open Finset

theorem AdvancedEncryption.WE.XWE.hybrid_gain_budget (m : ℕ) (p C : ℕ → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hop : ∀ j < m, K * (p (j + 1) - p j) ^ 2 ≤ C j) :
    K * (p m - p 0) ^ 2 ≤ (m : ℝ) * ∑ j ∈ range m, C j := by
  sorry
