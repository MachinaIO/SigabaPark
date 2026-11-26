import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.Common

theorem solution {R : Type*} [Ring R] {a b c d : Type*}
    [Fintype b] [Fintype c]
    (S : Matrix a b R) (A : Matrix b c R) (E' : Matrix a c R) (D : Matrix c d R)
    (E : Matrix b d R)
    (hAD : A * D = E) :
    (S * A + E') * D = S * E + E' * D := by
  rw [Matrix.add_mul, Matrix.mul_assoc, hAD]
