import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.Common

theorem solution {R : Type*} [Ring R] {r r' n m : Type*}
    [Fintype r] [Fintype n]
    (V' : Matrix r' n R) (S : Matrix n n R) (K : Matrix r' r R) (V : Matrix r n R)
    (A : Matrix n m R) (E : Matrix n m R) (hX : V' * S = K * V) :
    V' * (S * A + E) = K * (V * A) + V' * E := by
  rw [Matrix.mul_add, ← Matrix.mul_assoc, hX, Matrix.mul_assoc]
