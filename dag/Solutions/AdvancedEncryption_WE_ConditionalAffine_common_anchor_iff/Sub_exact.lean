import Mathlib

theorem solution {F V : Type} [Field F] [AddCommGroup V] [Module F V]
    (K : Submodule F V) (b : V) :
    (∃ e : (V →ₗ[F] F) ≃ (V →ₗ[F] F), ∀ r,
      (∀ k ∈ K, (e r) k = r k) ∧ (e r) b = r b + 1) ↔ b ∉ K := by
  classical
  constructor
  · rintro ⟨e,he⟩ hb
    have h0 := (he 0).1 b hb
    have h1 := (he 0).2
    simp only [LinearMap.zero_apply, zero_add] at h0 h1
    exact one_ne_zero (h1.symm.trans h0)
  · intro hb
    have hq : K.mkQ b ≠ 0 := by
      exact fun hz => hb ((Submodule.Quotient.mk_eq_zero K).mp hz)
    obtain ⟨g,hg⟩ := Module.Projective.exists_dual_eq_one F hq
    let u := g.comp K.mkQ
    have hu : ∀ k ∈ K, u k = 0 := by
      intro k hk
      have hz : K.mkQ k = 0 := (Submodule.Quotient.mk_eq_zero K).mpr hk
      change g (K.mkQ k) = 0
      rw [hz, map_zero]
    refine ⟨{ toFun := fun r => r+u
              invFun := fun r => r-u
              left_inv := fun r => by simp
              right_inv := fun r => by simp }, ?_⟩
    intro r
    constructor
    · intro k hk
      change r k + u k = r k
      simp [hu k hk]
    · change r b + g (K.mkQ b) = r b + 1
      rw [hg]
