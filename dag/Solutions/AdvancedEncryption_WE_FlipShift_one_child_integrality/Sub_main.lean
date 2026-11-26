import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Common
import Mathlib.Tactic.Abel

open Matrix

theorem solution {X κ μ : Type*} [Fintype X] [DecidableEq X] [Fintype κ] [Fintype μ]
    [DecidableEq μ] (c : X → κ → ℚ) (t : X) (α : X → ℚ) (hαt : α t = 1)
    (hrel : ∑ x, α x • c x = 0)
    (Δ : ℤ) (hΔ : ∀ x, ∃ a : ℤ, (Δ : ℚ) * α x = a)
    (M : Matrix κ μ ℚ) (D : Matrix μ μ ℚ) (hD : IsUnit D.det)
    (e : X → μ → ℤ) (f : μ → ℚ) :
    ∃ z : μ → ℤ,
      (Δ : ℚ) • (∑ x, α x • ((c x ᵥ* M + (fun j => (e x j : ℚ)) ᵥ* D) ᵥ* D⁻¹)) =
        (fun j => (z j : ℚ)) ∧
      (Δ : ℚ) • (∑ x, α x • ((c x ᵥ* M + (fun j => (e x j : ℚ)) ᵥ* D +
          (if x = t then f else 0)) ᵥ* D⁻¹)) =
        (fun j => (z j : ℚ)) + (Δ : ℚ) • (f ᵥ* D⁻¹) := by
  choose a ha using hΔ
  have hcancel : ∀ v : μ → ℚ, v ᵥ* D ᵥ* D⁻¹ = v := by
    intro v; rw [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hD, Matrix.vecMul_one]
  have hterm : ∀ x, (c x ᵥ* M + (fun j => (e x j : ℚ)) ᵥ* D) ᵥ* D⁻¹ =
      c x ᵥ* (M * D⁻¹) + (fun j => (e x j : ℚ)) := by
    intro x
    rw [Matrix.add_vecMul, hcancel, Matrix.vecMul_vecMul]
  have hsum : ∑ x, α x • ((c x ᵥ* M + (fun j => (e x j : ℚ)) ᵥ* D) ᵥ* D⁻¹) =
      ∑ x, α x • (fun j => (e x j : ℚ)) := by
    simp_rw [hterm, smul_add, Finset.sum_add_distrib, ← Matrix.smul_vecMul,
      ← Matrix.sum_vecMul, hrel, Matrix.zero_vecMul, zero_add]
  refine ⟨fun j => ∑ x, a x * e x j, ?_, ?_⟩
  · rw [hsum]
    funext j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Int.cast_sum, Int.cast_mul,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← ha x]; ring
  · have hsplit : ∀ x, (c x ᵥ* M + (fun j => (e x j : ℚ)) ᵥ* D + (if x = t then f else 0)) ᵥ* D⁻¹ =
        (c x ᵥ* M + (fun j => (e x j : ℚ)) ᵥ* D) ᵥ* D⁻¹ +
          (if x = t then f ᵥ* D⁻¹ else 0) := by
      intro x
      by_cases hx : x = t
      · simp only [hx, ite_true, Matrix.add_vecMul]
      · simp only [hx, ite_false, add_zero]
    simp_rw [hsplit, smul_add, Finset.sum_add_distrib, smul_ite, smul_zero]
    rw [Finset.sum_ite_eq' Finset.univ t]
    simp only [Finset.mem_univ, ite_true, hαt, one_smul]
    rw [smul_add, hsum]
    congr 1
    funext j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Int.cast_sum, Int.cast_mul,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← ha x]; ring
