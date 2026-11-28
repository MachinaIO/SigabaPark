import Mathlib

theorem solution {F V W U : Type} [Field F] [AddCommGroup V] [Module F V]
    [AddCommGroup W] [Module F W] [AddCommGroup U] [Module F U]
    (A : V →ₗ[F] W) (d : W) (align : W ≃ₗ[F] U) (w : V) :
    (align.toLinearMap.comp A) w = align d ↔ A w = d := by
  exact align.injective.eq_iff
