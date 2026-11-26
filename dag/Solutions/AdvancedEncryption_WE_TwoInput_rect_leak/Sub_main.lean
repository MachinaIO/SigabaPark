import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.Ring

theorem solution {R : Type} [CommRing R] {r c : Type} [Fintype r]
    (a a' b b' : r → R) (A G : Matrix r c R) (p p' : R) (e1 e2 e3 e4 : c → R) :
    (Matrix.vecMul (a + b) (A - p • G) + e1) - (Matrix.vecMul (a' + b) (A - p' • G) + e2)
      - (Matrix.vecMul (a + b') (A - p • G) + e3) + (Matrix.vecMul (a' + b') (A - p' • G) + e4) =
      (p' - p) • Matrix.vecMul (b - b') G + (e1 - e2 - e3 + e4) := by
  simp only [Matrix.add_vecMul, Matrix.vecMul_sub, Matrix.vecMul_smul, Matrix.sub_vecMul]
  ext i
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring
