import Mathlib

theorem solution {K U V : Type*} [Field K] [Fintype K] [AddCommGroup U] [Module K U]
    [Fintype U] [AddCommGroup V] [Module K V] (L : U →ₗ[K] V) (c : V)
    (h : Module.Dual K V) :
    (h.comp L = 0 → ∀ b, h (L b + c) = h c) ∧
    (h.comp L ≠ 0 → ∀ z z' : K,
      {u : U | h (L u + c) = z}.ncard = {u : U | h (L u + c) = z'}.ncard) := by
  refine ⟨fun h0 b => ?_, fun hne z z' => ?_⟩
  · have : h (L b) = 0 := by simpa using LinearMap.congr_fun h0 b
    simp [map_add, this]
  · obtain ⟨u0, hu0⟩ : ∃ u0, (h.comp L) u0 ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hne (LinearMap.ext hc)
    have hd : h (L (((z' - z) / (h.comp L) u0) • u0)) = z' - z := by
      rw [map_smul, map_smul, smul_eq_mul]
      change (z' - z) / (h.comp L) u0 * (h.comp L) u0 = z' - z
      field_simp
    have e : ∀ u x : U, h (L (u + x) + c) = h (L u + c) + h (L x) := by
      intro u x; simp only [map_add]; ring
    apply Set.ncard_congr (fun u _ => u + ((z' - z) / (h.comp L) u0) • u0)
    · intro u hu
      simp only [Set.mem_setOf_eq] at hu ⊢
      rw [e, hu, hd]; ring
    · intro u v _ _ huv; simpa using huv
    · intro v hv
      refine ⟨v - ((z' - z) / (h.comp L) u0) • u0, ?_, by simp⟩
      simp only [Set.mem_setOf_eq] at hv ⊢
      have := e (v - ((z' - z) / (h.comp L) u0) • u0) (((z' - z) / (h.comp L) u0) • u0)
      rw [sub_add_cancel, hv, hd] at this
      linear_combination -this
