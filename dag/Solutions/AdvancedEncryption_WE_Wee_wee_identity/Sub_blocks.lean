import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic.Abel

open Matrix

theorem solution {K : Type*} [CommRing K] {ℓ n m mW k : ℕ}
    (B : Matrix (Fin n) (Fin m) K) (W : Fin ℓ → Matrix (Fin n) (Fin mW) K)
    (TB : Fin ℓ → Fin ℓ → Matrix (Fin m) (Fin k) K) (TW : Fin ℓ → Matrix (Fin mW) (Fin k) K)
    (G : Matrix (Fin n) (Fin k) K)
    (h : ∀ i j, B * TB i j + W i * TW j = if i = j then G else 0)
    (w : Fin ℓ → K) (R : Matrix (Fin m) (Fin mW) K) (j : Fin ℓ) :
    ((∑ i, w i • W i) + B * R) * TW j = B * (R * TW j - ∑ i, w i • TB i j) + w j • G := by
  have hW : ∀ i, W i * TW j = (if i = j then G else 0) - B * TB i j := fun i =>
    eq_sub_of_add_eq' (h i j)
  rw [Matrix.add_mul, Matrix.sum_mul, Matrix.mul_sub, Matrix.mul_sum, Matrix.mul_assoc]
  simp_rw [Matrix.smul_mul, hW, smul_sub, Matrix.mul_smul]
  rw [Finset.sum_sub_distrib]
  simp [smul_ite, Finset.sum_ite_eq']
  abel
