import Mathlib

theorem solution {V A : Type} [AddCommGroup V] [AddCommGroup A] (Q : V → A)
    (B : V → V →+ A) (hp : ∀ x y, Q (x+y) = Q x + Q y - Q 0 + B x y)
    (W : AddSubgroup V) (iso : ∀ x ∈ W, ∀ y ∈ W, B x y = 0) (t : V) :
    ∃ L : W →+ A, ∀ w : W, Q (t+w) = Q t + L w := by
  let L : W →+ A := {
    toFun := fun w => Q w - Q 0 + B t w
    map_zero' := by simp
    map_add' := by
      intro w v
      change Q ((w : V)+(v : V)) - Q 0 + B t (w+v) = _
      rw [hp, iso w w.property v v.property, map_add]
      abel }
  refine ⟨L, ?_⟩
  intro w
  change Q (t+w) = Q t + (Q w - Q 0 + B t w)
  rw [hp]
  abel
