import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Common

open Matrix

theorem solution {R ι κ μ ν : Type*} [CommRing R] [Fintype κ] [Fintype μ]
    (B : Matrix ι κ R) (C : Matrix κ μ R) (F : Matrix ι μ R) (K : Matrix μ ν R)
    (hC : C * K = 0) : (B * C + F) * K = F * K := by
  rw [Matrix.add_mul, Matrix.mul_assoc, hC, Matrix.mul_zero, zero_add]
