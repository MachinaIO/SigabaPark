import Mathlib

theorem AdvancedEncryption.WE.QuadraticResidual.isotropic_coset {V A : Type} [AddCommGroup V] [AddCommGroup A] (Q : V → A)
    (B : V → V →+ A) (hp : ∀ x y, Q (x+y) = Q x + Q y - Q 0 + B x y)
    (W : AddSubgroup V) (iso : ∀ x ∈ W, ∀ y ∈ W, B x y = 0) (t : V) :
    ∃ L : W →+ A, ∀ w : W, Q (t+w) = Q t + L w := by
  sorry
