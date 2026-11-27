import Mathlib

theorem solution {X Y Z : Type*} [AddCommGroup X] [AddCommGroup Y]
    (A : X →+ Y) (U : Z → X) (V G : Z → Y) (h : Z)
    (p : X) (r : Z) (z : Y) :
    ((∀ j, V j = A (U j) + G j) → A (-(U h)) + V h = G h) ∧
    ((∀ j, V j = A (U j)) → A p + V r = z → A (p + U r) = z) := by
  constructor
  · intro e
    rw [map_neg, e]
    abel
  · intro e hz
    simpa only [map_add, e] using hz
