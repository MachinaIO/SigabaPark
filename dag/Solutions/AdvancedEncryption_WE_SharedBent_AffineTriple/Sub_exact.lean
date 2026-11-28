import Mathlib

theorem solution {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] (l : V →ₗ[ZMod 2] ZMod 2)
    (u : ZMod 2) (x y z : V) :
    u + l (x+y+z) = (u+l x) + (u+l y) + (u+l z) := by
  have h : u + u = 0 := by revert u; decide
  rw [map_add, map_add]
  calc
    _ = (u+u) + (u + l x + l y + l z) := by rw [h]; abel
    _ = _ := by abel
