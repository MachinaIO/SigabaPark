import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.Common

theorem solution {R : Type*} [Ring R] {n m k : Type*}
    [Fintype n] [DecidableEq n] [Fintype m]
    (W Winv : Matrix n n R) (hW : Winv * W = 1)
    (A : Matrix n m R) (D : Matrix m k R) (Y : Matrix n k R) :
    A * D = Y ↔ (W * A) * D = W * Y := by
  constructor
  · intro h
    rw [Matrix.mul_assoc, h]
  · intro h
    have h2 : Winv * ((W * A) * D) = Winv * (W * Y) := by rw [h]
    rw [Matrix.mul_assoc W A D, ← Matrix.mul_assoc Winv W, hW, Matrix.one_mul,
      ← Matrix.mul_assoc Winv W, hW, Matrix.one_mul] at h2
    exact h2
