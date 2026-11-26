import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NoncommRing
import Mathlib.Logic.Equiv.Fin.Basic

open Matrix

theorem solution {K : Type*} [CommRing K] {k n : ℕ}
    (c : Kˣ) (Gm : Matrix (Fin k) (Fin n) K) (Ginv : Matrix (Fin n) (Fin n) K)
    (hG : Gm * Ginv = ((c⁻¹ : Kˣ) : K) • Gm) (s : Fin k → K) (e : Fin n → K) :
    (s ᵥ* ((c : K) • Gm) + e) ᵥ* Ginv = s ᵥ* Gm + e ᵥ* Ginv := by
  rw [Matrix.add_vecMul, Matrix.vecMul_vecMul, Matrix.smul_mul, hG, smul_smul,
    Units.mul_inv, one_smul]
