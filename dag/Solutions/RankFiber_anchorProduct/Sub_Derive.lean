import Mathlib.Tactic

theorem solution {R : Type*} [CommRing R] {I J : Type*}
    (a : I → R) (b : J → R) (i₀ : I) (j₀ : J) (h : a i₀ * b j₀ = 1)
    (i : I) (j : J) : (a i * b j₀) * (a i₀ * b j) = a i * b j := by
  calc
    _ = (a i * b j) * (a i₀ * b j₀) := by ring
    _ = a i * b j := by rw [h, mul_one]

