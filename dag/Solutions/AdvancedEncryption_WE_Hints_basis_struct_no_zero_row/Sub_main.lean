import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.Common

open Matrix

theorem solution {K ι μ : Type*} [Field K]
    [Fintype ι] [DecidableEq ι] [Fintype μ] (W : Matrix ι ι K) (hW : IsUnit W.det)
    (Rm : Matrix ι μ K) (Rr : Matrix μ ι K) (hR : Rm * Rr = 1) (c : ι → K)
    (hc : c ᵥ* (W⁻¹ * Rm) = 0) : c = 0 := by
  have h1 : c ᵥ* (W⁻¹ * Rm * Rr * W) = 0 := by
    rw [← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul, hc, Matrix.zero_vecMul,
      Matrix.zero_vecMul]
  rwa [Matrix.mul_assoc W⁻¹, hR, Matrix.mul_one, Matrix.nonsing_inv_mul _ hW,
    Matrix.vecMul_one] at h1
