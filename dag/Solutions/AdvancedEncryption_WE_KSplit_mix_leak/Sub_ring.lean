import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.Ring

theorem solution {R : Type} [CommRing R] {r c : Type} [Fintype r]
    (s : r → R) (A G : Matrix r c R) (x x' : R) (e e' : c → R) :
    (Matrix.vecMul s (A - x • G) + e) - (Matrix.vecMul s (A - x' • G) + e') =
      (x' - x) • Matrix.vecMul s G + (e - e') := by
  rw [Matrix.vecMul_sub, Matrix.vecMul_sub, Matrix.vecMul_smul, Matrix.vecMul_smul]
  ext i; simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
