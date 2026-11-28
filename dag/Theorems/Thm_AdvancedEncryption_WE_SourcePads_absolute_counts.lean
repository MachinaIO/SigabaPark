import Mathlib

open scoped BigOperators

theorem AdvancedEncryption.WE.SourcePads.absolute_counts {I : Type} [Fintype I] (d : I → ℝ) (bound : ℝ)
    (h : (∑ i, (d i)^2) ≤ bound) :
    (∑ i, |d i|)^2 ≤ (Fintype.card I : ℝ)*bound := by sorry
