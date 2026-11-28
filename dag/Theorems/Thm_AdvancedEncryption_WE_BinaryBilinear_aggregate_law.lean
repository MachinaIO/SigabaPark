import Definitions.Def_BinaryBilinearCounts
open BinaryBilinearCounts

theorem AdvancedEncryption.WE.BinaryBilinear.aggregate_law (j : ℕ) : (∀ a b, discrepancy (2*j) a b = 4^j * sign (a && b)) ∧
    (∀ a b, discrepancy (2*j+1) a b = 4^(j+1)*origin a b) := by
  sorry
