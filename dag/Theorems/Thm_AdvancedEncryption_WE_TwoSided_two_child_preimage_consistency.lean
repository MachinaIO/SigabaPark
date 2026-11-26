import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.Common

open Matrix

/-- **Two-child consistency of square preimages (note `pq-we-two-sided-lwe`, §3).** Square
invertible preimages `D₀, D₁` of targets `Y₀, Y₁` under one common matrix `A` exist iff
`Y₀ D₀⁻¹ = Y₁ D₁⁻¹`. Hence "preimage-first" simulation (sample `D_b`, then define `A`) cannot
give a row two independent structured targets, e.g. two independent small targets `f₀, f₁`. -/
theorem AdvancedEncryption.WE.TwoSided.two_child_preimage_consistency {K ι μ : Type*} [Field K] [Fintype μ] [DecidableEq μ]
    (Y₀ Y₁ : Matrix ι μ K) (D₀ D₁ : Matrix μ μ K) (hD₀ : IsUnit D₀.det) (hD₁ : IsUnit D₁.det) :
    (∃ A : Matrix ι μ K, A * D₀ = Y₀ ∧ A * D₁ = Y₁) ↔ Y₀ * D₀⁻¹ = Y₁ * D₁⁻¹ := by sorry
