import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.Common

theorem solution {R : Type*} [Ring R] {a b c d : Type*}
    [Fintype b] [Fintype c]
    (z : Matrix a b R) (S : Matrix b c R) (A : Matrix c d R) (E : Matrix b d R)
    (hz : z * S = 0) :
    z * (S * A + E) = z * E := by
  rw [Matrix.mul_add, ← Matrix.mul_assoc, hz, Matrix.zero_mul, zero_add]
