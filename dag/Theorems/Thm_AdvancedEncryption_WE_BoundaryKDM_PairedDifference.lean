import Mathlib

theorem AdvancedEncryption.WE.BoundaryKDM.PairedDifference {I : Type*} [Fintype I] (weight val : I → ℝ) :
    (∑ i, ∑ j, (weight i * val i) * (weight j * val j)) =
    (∑ i, weight i * val i)^2 := by sorry
