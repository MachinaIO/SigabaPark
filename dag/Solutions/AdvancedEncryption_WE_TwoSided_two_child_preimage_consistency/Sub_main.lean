import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.Common

open Matrix

theorem solution {K ι μ : Type*} [Field K] [Fintype μ] [DecidableEq μ]
    (Y₀ Y₁ : Matrix ι μ K) (D₀ D₁ : Matrix μ μ K) (hD₀ : IsUnit D₀.det) (hD₁ : IsUnit D₁.det) :
    (∃ A : Matrix ι μ K, A * D₀ = Y₀ ∧ A * D₁ = Y₁) ↔ Y₀ * D₀⁻¹ = Y₁ * D₁⁻¹ := by
  constructor
  · rintro ⟨A, h0, h1⟩
    rw [← h0, ← h1, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hD₀, Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ hD₁]
  · intro h
    refine ⟨Y₀ * D₀⁻¹, ?_, ?_⟩
    · rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hD₀, Matrix.mul_one]
    · rw [h, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hD₁, Matrix.mul_one]
