import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic.Common

theorem solution {K : Type*} [Field K] {V U ι J : Type*} [Fintype V] [Fintype ι] [Fintype J]
    [DecidableEq ι]
    (X : V → ι → K) (L : ℕ → (ι → K) →ₗ[K] (U → K)) (col : J → ℕ × U) :
    (Matrix.of fun x j => L ((col j).1 + 1) (X x) (col j).2 - L (col j).1 (X x) (col j).2).rank
      ≤ Fintype.card ι := by
  have hfac : (Matrix.of fun x j => L ((col j).1 + 1) (X x) (col j).2 - L (col j).1 (X x) (col j).2)
      = Matrix.of X * Matrix.of (fun k j => L ((col j).1 + 1) (Pi.single k 1) (col j).2
          - L (col j).1 (Pi.single k 1) (col j).2) := by
    ext x j
    simp only [Matrix.of_apply, Matrix.mul_apply]
    have e : ∀ M : (ι → K) →ₗ[K] (U → K), M (X x) = ∑ k, X x k • M (Pi.single k 1) := by
      intro M
      conv_lhs => rw [← Finset.univ_sum_single (X x)]
      rw [map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← map_smul]; congr 1; ext i; by_cases h : i = k <;> simp [h]
    rw [e (L ((col j).1 + 1)), e (L (col j).1)]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, ← Finset.sum_sub_distrib, mul_sub]
  rw [hfac]
  exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_le_card_width _)
