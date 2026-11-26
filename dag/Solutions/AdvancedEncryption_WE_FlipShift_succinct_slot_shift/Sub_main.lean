import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.Common
import Mathlib.Tactic.Abel

open Matrix

theorem solution {R : Type*} [CommRing R] {n m m' g p : Type*} [Fintype n] [Fintype m]
    [Fintype m'] [Fintype g]
    (B : Matrix n m R) (Wk : Matrix n m' R) (Tk : Matrix m g R) (TW : Matrix m' g R)
    (G : Matrix n g R) (h : B * Tk + Wk * TW = G) (Z : Matrix g p R) (s : n → R) (e : m → R) :
    (s ᵥ* B + e) ᵥ* (Tk * Z) = s ᵥ* (G * Z) - (s ᵥ* Wk) ᵥ* (TW * Z) + e ᵥ* (Tk * Z) := by
  rw [← h]
  simp only [Matrix.add_vecMul, Matrix.add_mul, Matrix.vecMul_add, Matrix.vecMul_vecMul,
    Matrix.mul_assoc]
  abel
