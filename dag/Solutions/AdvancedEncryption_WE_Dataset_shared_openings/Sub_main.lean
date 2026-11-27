import Mathlib

theorem solution {X Y I : Type*} [AddCommGroup X] [AddCommGroup Y]
    (A : X →+ Y) (u₀ u₁ : I → X) (V G : I → Y)
    (h₀ : ∀ i, A (u₀ i) = V i) (h₁ : ∀ i, A (u₁ i) + G i = V i)
    (h : I) : A (u₀ h - u₁ h) = G h := by
  rw [map_sub, h₀, ← h₁]
  abel
