import Mathlib

theorem AdvancedEncryption.WE.BoundaryKDM.RetainType {I : Type*} [Fintype I] [DecidableEq I] (prob gap : I → ℝ) (j : I)
    (hp : ∀ i, 0 ≤ prob i) : prob j*(gap j)^2 ≤ ∑ i, prob i*(gap i)^2 := by sorry
