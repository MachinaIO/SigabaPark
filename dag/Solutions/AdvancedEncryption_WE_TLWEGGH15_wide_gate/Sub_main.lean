import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.Common

open Matrix
open scoped Kronecker

theorem solution {R : Type*} [CommRing R] {ι κ ν μ : Type*} [Fintype κ] [Fintype ν] [DecidableEq ν]
    {ι' : Type*} (X : Matrix ι κ R) (Y : Matrix ι' ν R) (M : Matrix κ κ R)
    (F : Matrix (κ × ν) μ R) :
    (X ⊗ₖ Y) * ((M ⊗ₖ (1 : Matrix ν ν R)) * F) = ((X * M) ⊗ₖ Y) * F := by
  rw [← Matrix.mul_assoc, ← Matrix.mul_kronecker_mul, Matrix.mul_one]
