import Mathlib

theorem AdvancedEncryption.WE.ConditionalAffine.common_anchor_iff {F V : Type} [Field F] [AddCommGroup V] [Module F V]
    (K : Submodule F V) (b : V) :
    (∃ e : (V →ₗ[F] F) ≃ (V →ₗ[F] F), ∀ r,
      (∀ k ∈ K, (e r) k = r k) ∧ (e r) b = r b + 1) ↔ b ∉ K := by
  sorry
