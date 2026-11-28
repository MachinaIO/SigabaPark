import Mathlib

theorem AdvancedEncryption.WE.SharedBent.GramTarget {V ι : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype ι]
    (a : ι → V) (w : ι → ZMod 2)
    (M : Module.Dual (ZMod 2) V →ₗ[ZMod 2] V)
    (hM : ∀ f : Module.Dual (ZMod 2) V, f (M f) = ∑ i, w i * (f (a i) * f (a i))) :
    (∑ i, w i • a i) ∈ M.range := by sorry
