import Definitions.Def_GGH15

open Matrix AdvancedEncryption.WE.GGH15

theorem solution {R : Type} [CommRing R] {w n : Type} [Fintype w] [DecidableEq w]
    [Fintype n] [DecidableEq n] (M M' : Matrix w w R) (S S' : Matrix n n R) :
    gammaTensorDiag M S * gammaTensorDiag M' S' = gammaTensorDiag (M * M') (S * S') := by
  simp only [gammaTensorDiag, gammaTensor, fromBlocks_multiply, Matrix.mul_zero,
    Matrix.zero_mul, add_zero, zero_add]
  rw [← Matrix.mul_kronecker_mul]
