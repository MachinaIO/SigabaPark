import Mathlib

theorem solution {V U R : Type*} [AddCommGroup V] [AddCommGroup U] [AddCommGroup R]
    (L : V →+ U) (f : V →+ R) (x k : V) (δ : R) (hk : L k = 0) (hf : f k = δ) :
    (L (x+k), f (x+k)) = (L x, f x + δ) := by
  simp [map_add, hk, hf]
