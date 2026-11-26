import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Tactic.LinearCombination

open Matrix

theorem solution {K : Type*} [Field K] {m n k : ℕ}
    (A : Matrix (Fin m) (Fin m) K) (B : Matrix (Fin n) (Fin n) K) (hA : IsUnit A.det)
    (hB : IsUnit B.det) (M : Fin k → Matrix (Fin m) (Fin n) K) (a : Fin k → K) :
    (∑ j, a j • (A * M j * B)).rank = (∑ j, a j • M j).rank := by
  have h : (∑ j, a j • (A * M j * B)) = A * (∑ j, a j • M j) * B := by
    simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]
  rw [h, Matrix.rank_mul_eq_left_of_isUnit_det B _ hB,
    Matrix.rank_mul_eq_right_of_isUnit_det A _ hA]
