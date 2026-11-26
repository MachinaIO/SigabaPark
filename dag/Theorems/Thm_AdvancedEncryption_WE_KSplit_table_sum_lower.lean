import Mathlib.Analysis.MeanInequalities
open Finset

theorem AdvancedEncryption.WE.KSplit.table_sum_lower (k : ℕ) (hk : 0 < k) (N : Fin k → ℝ)
    (hN : ∀ i, 0 ≤ N i) (t : ℝ) (ht : 0 ≤ t) (hcov : t ^ k ≤ ∏ i, N i) :
    (k : ℝ) * t ≤ ∑ i, N i := by
  sorry
