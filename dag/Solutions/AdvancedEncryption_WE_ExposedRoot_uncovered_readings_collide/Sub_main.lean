import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.Common
import Mathlib.Tactic.Abel

theorem solution {R : Type*} [Ring R] {a b c d : Type*}
    [Fintype b] [Fintype c] [Fintype d]
    (Rv : Matrix a b R) (D1 : Matrix b c R) (R1 : Matrix a c R) (Am1 : Matrix c c R)
    (e1 : Matrix a c R)
    (D20 D21 : Matrix c d R) (R2 : Matrix c c R) (Am2 : Matrix c d R) (E0 E1 : Matrix c d R)
    (hR1 : Rv * D1 = R1 * Am1 + e1)
    (h0 : Am1 * D20 = R2 * Am2 + E0) (h1 : Am1 * D21 = R2 * Am2 + E1) :
    Rv * D1 * D20 - Rv * D1 * D21 = R1 * (E0 - E1) + e1 * (D20 - D21) := by
  rw [hR1, Matrix.add_mul, Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_assoc, h0, h1,
    Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_add, Matrix.mul_add]
  abel
