import Mathlib

theorem AdvancedEncryption.WE.OddFault.MaskRange {K V W : Type*} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (M : V →ₗ[K] W) (g : W) :
    (∀ z : K, ∃ u : V, ∀ v : V, M (v + u) = z • g + M v) ↔ g ∈ M.range := by sorry
