import Definitions.Def_BucketLabel
open BucketLabel
theorem AdvancedEncryption.WE.BucketLabel.hybridSquared {I : Type} [Fintype I] (g cost : I → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (h : ∀ i, M * (g i)^2 ≤ cost i) :
    M * (∑ i, g i)^2 ≤ (Fintype.card I : ℝ) * ∑ i, cost i := by sorry
