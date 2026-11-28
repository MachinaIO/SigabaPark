import Mathlib

theorem solution {V ι : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype ι]
    (a : ι → V) (w : ι → ZMod 2)
    (M : Module.Dual (ZMod 2) V →ₗ[ZMod 2] V)
    (hM : ∀ f : Module.Dual (ZMod 2) V, f (M f) = ∑ i, w i * (f (a i) * f (a i))) :
    (∑ i, w i • a i) ∈ M.range := by
  by_contra h
  have hq : M.range.mkQ (∑ i, w i • a i) ≠ 0 := by
    intro hz
    exact h ((Submodule.Quotient.mk_eq_zero _).mp hz)
  obtain ⟨u, hu⟩ := Module.Projective.exists_dual_eq_one (ZMod 2) hq
  let f := u.comp M.range.mkQ
  have hf : f (∑ i, w i • a i) = 1 := hu
  have hk : M.range.mkQ (M f) = 0 := (Submodule.Quotient.mk_eq_zero _).mpr ⟨f, rfl⟩
  have hzero : f (M f) = 0 := by simp only [f, LinearMap.comp_apply, hk, map_zero]
  have bit : ∀ x : ZMod 2, x*x = x := by decide
  have hsame : f (M f) = f (∑ i, w i • a i) := by
    rw [hM]
    simp only [bit, map_sum, map_smul, smul_eq_mul]
  exact zero_ne_one (hzero.symm.trans (hsame.trans hf))
