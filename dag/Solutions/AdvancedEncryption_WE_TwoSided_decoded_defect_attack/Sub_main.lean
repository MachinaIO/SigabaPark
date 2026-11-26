import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Tactic.Common

open Matrix

theorem solution {K X κ μ : Type*} [Field K]
    [Fintype X] [DecidableEq X] [Fintype κ] [Fintype μ] [DecidableEq μ]
    (c : X → κ → K) (t : X)
    (hspan : c t ∈ Submodule.span K (Set.range fun x : {x : X // x ≠ t} => c x))
    (E₀ E₁ : Matrix κ μ K) (D₀ D₁ : Matrix μ μ K) (hD₀ : IsUnit D₀.det) (hD₁ : IsUnit D₁.det)
    (e : X → μ → K) (f₀ f₁ : μ → K) :
    ∃ α : X → K, α t = 1 ∧
      (∑ x, α x • ((c x ᵥ* E₀ + e x ᵥ* D₀) ᵥ* D₀⁻¹ - (c x ᵥ* E₁ + e x ᵥ* D₁) ᵥ* D₁⁻¹) = 0) ∧
      (∑ x, α x • ((c x ᵥ* E₀ + e x ᵥ* D₀ + (if x = t then f₀ else 0)) ᵥ* D₀⁻¹ -
          (c x ᵥ* E₁ + e x ᵥ* D₁ + (if x = t then f₁ else 0)) ᵥ* D₁⁻¹) =
        f₀ ᵥ* D₀⁻¹ - f₁ ᵥ* D₁⁻¹) := by
  obtain ⟨γ, hγ⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hspan
  set α : X → K := fun x => if h : x = t then 1 else -γ ⟨x, h⟩ with hα
  have hsum : ∑ x, α x • c x = 0 := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ t)]
    have h1 : ∑ x ∈ Finset.univ.erase t, α x • c x = -∑ y : {x : X // x ≠ t}, γ y • c y := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_bij' (fun x hx => (⟨x, Finset.ne_of_mem_erase hx⟩ : {x : X // x ≠ t}))
        (fun y _ => y.1) (fun _ _ => Finset.mem_univ _)
        (fun y _ => Finset.mem_erase.2 ⟨y.2, Finset.mem_univ _⟩)
        (fun _ _ => rfl) (fun _ _ => rfl) ?_
      intro x hx
      simp [hα, Finset.ne_of_mem_erase hx]
    rw [h1, hγ]; simp [hα]
  have hcancel : ∀ (D : Matrix μ μ K), IsUnit D.det → ∀ v : μ → K, v ᵥ* D ᵥ* D⁻¹ = v := by
    intro D hD v; rw [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hD, Matrix.vecMul_one]
  have hterm : ∀ x, (c x ᵥ* E₀ + e x ᵥ* D₀) ᵥ* D₀⁻¹ - (c x ᵥ* E₁ + e x ᵥ* D₁) ᵥ* D₁⁻¹ =
      c x ᵥ* (E₀ * D₀⁻¹ - E₁ * D₁⁻¹) := by
    intro x
    rw [Matrix.add_vecMul, Matrix.add_vecMul, hcancel D₀ hD₀, hcancel D₁ hD₁,
      Matrix.vecMul_sub, Matrix.vecMul_vecMul, Matrix.vecMul_vecMul]
    abel
  have hmain : ∑ x, α x • ((c x ᵥ* E₀ + e x ᵥ* D₀) ᵥ* D₀⁻¹ - (c x ᵥ* E₁ + e x ᵥ* D₁) ᵥ* D₁⁻¹)
      = 0 := by
    simp_rw [hterm, ← Matrix.smul_vecMul, ← Matrix.sum_vecMul, hsum, Matrix.zero_vecMul]
  refine ⟨α, by simp [hα], hmain, ?_⟩
  have hsplit : ∀ x, (c x ᵥ* E₀ + e x ᵥ* D₀ + (if x = t then f₀ else 0)) ᵥ* D₀⁻¹ -
      (c x ᵥ* E₁ + e x ᵥ* D₁ + (if x = t then f₁ else 0)) ᵥ* D₁⁻¹ =
      ((c x ᵥ* E₀ + e x ᵥ* D₀) ᵥ* D₀⁻¹ - (c x ᵥ* E₁ + e x ᵥ* D₁) ᵥ* D₁⁻¹) +
        (if x = t then f₀ ᵥ* D₀⁻¹ - f₁ ᵥ* D₁⁻¹ else 0) := by
    intro x
    by_cases hx : x = t
    · simp only [hx, ite_true, Matrix.add_vecMul]; abel
    · simp only [hx, ite_false, add_zero]
  simp_rw [hsplit, smul_add, Finset.sum_add_distrib, hmain, zero_add, smul_ite, smul_zero]
  rw [Finset.sum_ite_eq' Finset.univ t]
  simp [hα]
