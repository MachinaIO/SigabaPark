import Mathlib

theorem solution {K V W : Type*} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (M : V →ₗ[K] W) (g : W) (h : g ∉ M.range) :
    ∃ f : W →ₗ[K] K, ∀ (z : K) (v : V), f (z • g + M v) = z := by
  have hq : M.range.mkQ g ≠ 0 := by simpa using h
  obtain ⟨u, hu⟩ := Module.Projective.exists_dual_eq_one K hq
  refine ⟨u.comp M.range.mkQ, ?_⟩
  intro z v
  have hv : M.range.mkQ (M v) = 0 := (Submodule.Quotient.mk_eq_zero _).mpr ⟨v, rfl⟩
  simp only [LinearMap.comp_apply, map_add, map_smul, hu, hv, map_zero, smul_eq_mul, mul_one, add_zero]
