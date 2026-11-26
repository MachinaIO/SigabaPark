import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic.Common

theorem solution {K : Type*} [Field K] {U ι : Type*} [Fintype ι] [DecidableEq ι] (m : ℕ)
    (Y : Fin m → ι → K) (L : ℕ → (ι → K) →ₗ[K] (U → K)) (t : Fin m → ℕ) (u : Fin m → U)
    (hdiag : ∀ a, L (t a + 1) (Y a) (u a) ≠ L (t a) (Y a) (u a))
    (htri : ∀ a b, a < b → L (t b + 1) (Y a) (u b) = L (t b) (Y a) (u b)) :
    m ≤ Fintype.card ι := by
  set M : Matrix (Fin m) (Fin m) K := Matrix.of fun a b => L (t b + 1) (Y a) (u b) - L (t b) (Y a) (u b)
    with hM
  have hfac : M = Matrix.of Y * Matrix.of (fun k b => L (t b + 1) (Pi.single k 1) (u b)
          - L (t b) (Pi.single k 1) (u b)) := by
    ext a b
    simp only [hM, Matrix.of_apply, Matrix.mul_apply]
    have e : ∀ N : (ι → K) →ₗ[K] (U → K), N (Y a) = ∑ k, Y a k • N (Pi.single k 1) := by
      intro N
      conv_lhs => rw [← Finset.univ_sum_single (Y a)]
      rw [map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← map_smul]; congr 1; ext i; by_cases h : i = k <;> simp [h]
    rw [e (L (t b + 1)), e (L (t b))]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, ← Finset.sum_sub_distrib, mul_sub]
  have htr : M.BlockTriangular OrderDual.toDual := by
    intro a b hab
    have : a < b := hab
    simp only [hM, Matrix.of_apply, htri a b this, sub_self]
  have hdet : M.det ≠ 0 := by
    rw [Matrix.det_of_isLowerTriangular M htr, Finset.prod_ne_zero_iff]
    intro a _
    simp only [hM, Matrix.of_apply]
    exact sub_ne_zero.mpr (hdiag a)
  have hrank : M.rank = m := by
    have hu : IsUnit M := (Matrix.isUnit_iff_isUnit_det M).mpr (isUnit_iff_ne_zero.mpr hdet)
    simpa using Matrix.rank_of_isUnit (n := Fin m) M hu
  have h2 := Matrix.rank_le_card_width (Matrix.of Y)
  rw [← hrank, hfac]
  exact (Matrix.rank_mul_le_left _ _).trans h2
