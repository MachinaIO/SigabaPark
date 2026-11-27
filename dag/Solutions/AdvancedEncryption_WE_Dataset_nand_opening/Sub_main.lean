import Mathlib

theorem solution {X Y Z : Type*} [AddCommGroup X] [AddCommGroup Y]
    (A : X →+ Y) (U₁ U₂ : Z → X) (V₁ V₂ G : Z → Y) (R : Z → Z)
    (a b : Bool) (e₁ : ∀ j, V₁ j = A (U₁ j) + (if a then G j else 0))
    (e₂ : ∀ j, V₂ j = A (U₂ j) + (if b then G j else 0))
    (digit : ∀ j, G (R j) = V₁ j) (j : Z) :
    A (-((if b then U₁ j else 0) + U₂ (R j))) +
      (if !(a && b) then G j else 0) = G j - V₂ (R j) := by
  rw [e₂, digit, e₁]
  cases a <;> cases b <;> simp <;> abel
