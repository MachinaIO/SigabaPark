import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Common

open Matrix

theorem solution {R ν μ : Type*} [CommRing R] [Fintype μ]
    (ac am : Matrix ν μ R) (D : Matrix μ μ R) (T E1 E2 : Matrix ν μ R)
    (hc : ac * D = T + E1) (hm : am * D = T + E2) :
    (ac - am) * D = E1 - E2 := by
  rw [Matrix.sub_mul, hc, hm]; abel
