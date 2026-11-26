import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NoncommRing
import Mathlib.Logic.Equiv.Fin.Basic

open Matrix

theorem solution {K : Type*} [CommRing K] {k n N : ℕ}
    (Gm : Matrix (Fin k) (Fin n) K) (Z : Matrix (Fin k) (Fin N) K)
    (X : Matrix (Fin n) (Fin n) K) (H : Matrix (Fin N) (Fin n) K) (f : K)
    (hkey : Gm * X - f • Gm = Z * H) (s : Fin k → K) (e : Fin N → K) :
    (s ᵥ* Z + e) ᵥ* H = s ᵥ* (Gm * X) - f • (s ᵥ* Gm) + e ᵥ* H := by
  rw [Matrix.add_vecMul, Matrix.vecMul_vecMul, ← hkey, Matrix.vecMul_sub, Matrix.vecMul_smul]
