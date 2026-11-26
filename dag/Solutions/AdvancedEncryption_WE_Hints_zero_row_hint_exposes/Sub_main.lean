import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.Common

open Matrix

theorem solution {R ι μ ν : Type*} [CommRing R]
    [Fintype ι] [Fintype μ] (H : Matrix ι μ R) (X : Matrix μ ν R) (c : ι → R) (f : ν → R)
    (hf : c ᵥ* (H * X) = f) (σ : R) (e : μ → R) :
    (σ • (c ᵥ* H) + e) ᵥ* X = σ • f + e ᵥ* X := by
  rw [Matrix.add_vecMul, Matrix.smul_vecMul, Matrix.vecMul_vecMul, hf]
