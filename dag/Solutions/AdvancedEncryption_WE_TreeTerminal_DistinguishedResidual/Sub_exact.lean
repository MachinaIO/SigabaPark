import Mathlib

theorem solution {R : Type*} [CommRing R] (v a s d r e h : R)
    (expansion : v = s * (d*r) + h) (reference : a = s*d+e) :
    v-a*r = h-e*r := by
  rw [expansion, reference]
  ring
