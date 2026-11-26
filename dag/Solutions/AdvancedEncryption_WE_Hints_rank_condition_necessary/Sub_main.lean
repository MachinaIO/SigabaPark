import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.Common

open Matrix

theorem solution {R κ L μ : Type*} [CommRing R]
    [Fintype κ] [Fintype L] [Fintype μ] (M : Matrix κ L R) (B : Matrix L μ R) (c : κ → R)
    (u : L → R) (hu : u = c ᵥ* M) (y : μ → R) (t : κ → R) (hy : (M * B) *ᵥ y = t)
    (σ : R) (e : μ → R) :
    (σ • (u ᵥ* B) + e) ⬝ᵥ y = σ * (c ⬝ᵥ t) + e ⬝ᵥ y := by
  subst hu; subst hy
  rw [add_dotProduct, smul_dotProduct, smul_eq_mul, Matrix.vecMul_vecMul,
    Matrix.dotProduct_mulVec]
