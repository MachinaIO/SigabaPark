import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Basic.Real.Basic

theorem solution {K U V : Type*} [Field K] [AddCommGroup U]
    [Module K U] [Fintype U] [AddCommGroup V] [Module K V] (L : U →ₗ[K] V) (t : V) :
    (t ∈ LinearMap.range L →
      ∀ (f : V → ℝ) (e : V) (β : K), ∑ u, f (L u + e + β • t) = ∑ u, f (L u + e)) ∧
    (t ∉ LinearMap.range L → ∃ h : Module.Dual K V, h.comp L = 0 ∧ h t = 1) ∧
    (∀ h : Module.Dual K V, h.comp L = 0 →
      ∀ (u : U) (e : V) (β : K), h (L u + e + β • t) = h e + β * h t) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨l, rfl⟩ f e β
    have key : ∀ u, L u + e + β • L l = L (u + β • l) + e := by
      intro u; rw [map_add, map_smul]; abel
    simp_rw [key]
    exact Fintype.sum_equiv (Equiv.addRight (β • l)) _ _ (fun u => rfl)
  · intro ht
    obtain ⟨g, hg, hmap⟩ := Submodule.exists_dual_map_eq_bot_of_notMem ht inferInstance
    refine ⟨(g t)⁻¹ • g, ?_, ?_⟩
    · ext u
      have : g (L u) ∈ (LinearMap.range L).map g := ⟨L u, ⟨u, rfl⟩, rfl⟩
      rw [hmap] at this
      simp [(Submodule.mem_bot K).mp this]
    · simp [hg]
  · intro h hL u e β
    have : h (L u) = 0 := by simpa using LinearMap.congr_fun hL u
    simp [map_add, map_smul, this]
