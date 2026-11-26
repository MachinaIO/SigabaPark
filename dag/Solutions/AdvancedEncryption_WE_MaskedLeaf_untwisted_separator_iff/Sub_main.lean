import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Common
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

open Matrix

theorem solution {K : Type*} [Field K] {ι κ ν : Type*} [Fintype κ] [Fintype ν]
    [DecidableEq κ] (U : ι → Finset κ) (j : κ → K) (hj : ∀ k, j k ≠ 0) (v : ν → K)
    (hv : v ≠ 0) :
    (∃ ℓ : κ × ν → K, ∀ z,
        (fun p : κ × ν => (if p.1 ∈ U z then j p.1 else 0) * v p.2) ⬝ᵥ ℓ = 1) ↔
      ∃ lam : κ → K, ∀ z, ∑ k ∈ U z, lam k = 1 := by
  classical
  have key : ∀ (ℓ : κ × ν → K) z,
      (fun p : κ × ν => (if p.1 ∈ U z then j p.1 else 0) * v p.2) ⬝ᵥ ℓ =
        ∑ k ∈ U z, j k * ∑ i, v i * ℓ (k, i) := by
    intro ℓ z
    rw [dotProduct, Fintype.sum_prod_type, ← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun k => k ∈ U z)]
    have h1 : ∑ x ∈ Finset.univ.filter (fun k => k ∉ U z),
        ∑ y, (if x ∈ U z then j x else 0) * v y * ℓ (x, y) = 0 :=
      Finset.sum_eq_zero fun x hx => by
        simp only [Finset.mem_filter] at hx; simp [hx.2]
    rw [h1, add_zero, Finset.filter_mem_eq_inter, Finset.univ_inter]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_
    simp [hk]; ring
  constructor
  · rintro ⟨ℓ, hℓ⟩
    exact ⟨fun k => j k * ∑ i, v i * ℓ (k, i), fun z => by rw [← key]; exact hℓ z⟩
  · rintro ⟨lam, hlam⟩
    obtain ⟨i₀, hi₀⟩ : ∃ i, v i ≠ 0 := by
      by_contra h
      exact hv (funext fun i => by
        by_contra hi
        exact h ⟨i, hi⟩)
    refine ⟨fun p => if p.2 = i₀ then lam p.1 / (j p.1 * v i₀) else 0, fun z => ?_⟩
    rw [key, ← hlam z]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_eq_single i₀ (fun i _ hi => by simp [hi]) (by simp)]
    simp only [ite_true]
    field_simp [hj k, hi₀]
