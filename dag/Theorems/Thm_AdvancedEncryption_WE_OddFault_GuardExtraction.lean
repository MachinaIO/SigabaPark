import Mathlib

theorem AdvancedEncryption.WE.OddFault.GuardExtraction {K V W : Type*} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (M : V →ₗ[K] W) (g : W) (h : g ∉ M.range) :
    ∃ f : W →ₗ[K] K, ∀ (z : K) (v : V), f (z • g + M v) = z := by sorry
