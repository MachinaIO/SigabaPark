import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Common

open Matrix

theorem solution {R ι μ ν : Type*} [CommRing R] [Fintype ι] [Fintype μ] [DecidableEq μ]
    (S : Matrix ν ι R) (A : Matrix ι μ R) (D Dinv : Matrix μ μ R) (E : Matrix ι μ R)
    (E' : Matrix ν μ R) (hA : A * D = E) (hD : D * Dinv = 1) :
    S * A + E' = (S * E + E' * D) * Dinv := by
  rw [← hA, Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc, hD,
    Matrix.mul_one, Matrix.mul_one]
