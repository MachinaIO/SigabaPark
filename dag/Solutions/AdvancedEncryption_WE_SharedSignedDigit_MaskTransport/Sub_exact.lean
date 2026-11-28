import Mathlib

theorem solution {V R : Type*} [AddCommGroup V] [AddCommGroup R]
    (L : V →+ R) (s d : V) (m : R) :
    (L s + m) - L (s + d) = m - L d := by
  rw [map_add]
  abel
