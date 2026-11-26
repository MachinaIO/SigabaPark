import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.Common

open Matrix

theorem solution {R : Type*} [CommRing R] {κ μ ν : Type*} [Fintype κ] [Fintype μ] [DecidableEq μ]
    (B E : Matrix κ μ R) (D : Matrix μ μ R) (hD : IsUnit D.det) (hBD : B * D = E) :
    B = E * D⁻¹ ∧ ∀ (c : κ → R) (D' : Matrix μ ν R), c ᵥ* (B * D') = (c ᵥ* E) ᵥ* (D⁻¹ * D') := by
  have hB : B = E * D⁻¹ := by
    rw [← hBD, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hD, Matrix.mul_one]
  refine ⟨hB, fun c D' => ?_⟩
  rw [hB, Matrix.vecMul_vecMul, Matrix.mul_assoc]
