import SigabaNeoStd.Lattices.Homomorphic.Eval
import Mathlib.Tactic.Abel

open Matrix SigabaNeo.Lattices

theorem solution {K : Type*} [CommRing K] {ℓ n m mW k : ℕ}
    (Γ : GadgetMatrix K (Fin n) (Fin k))
    (B : Matrix (Fin n) (Fin m) K) (W : Fin ℓ → Matrix (Fin n) (Fin mW) K)
    (TB : Fin ℓ → Fin ℓ → Matrix (Fin m) (Fin k) K) (TW : Fin ℓ → Matrix (Fin mW) (Fin k) K)
    (h : ∀ i j, B * TB i j + W i * TW j = if i = j then Γ.G else 0)
    (w : Fin ℓ → K) (R : Matrix (Fin m) (Fin mW) K) (φ : Circuit (Fin ℓ))
    (hφ : φ.eval w = 0) :
    evalMat Γ (fun j => ((∑ i, w i • W i) + B * R) * TW j) φ - Γ.G =
      B * evalSim Γ (fun j => ((∑ i, w i • W i) + B * R) * TW j) w
        (fun j => R * TW j - ∑ i, w i • TB i j) φ - Γ.G := by
  have hA : ∀ j, ((∑ i, w i • W i) + B * R) * TW j =
      B * (R * TW j - ∑ i, w i • TB i j) + w j • Γ.G := by
    intro j
    have hW : ∀ i, W i * TW j = (if i = j then Γ.G else 0) - B * TB i j := fun i =>
      eq_sub_of_add_eq' (h i j)
    rw [Matrix.add_mul, Matrix.sum_mul, Matrix.mul_sub, Matrix.mul_sum, Matrix.mul_assoc]
    simp_rw [Matrix.smul_mul, hW, smul_sub, Matrix.mul_smul]
    rw [Finset.sum_sub_distrib]
    simp [smul_ite, Finset.sum_ite_eq']
    abel
  rw [sim_relation Γ B _ w _ hA φ, hφ, zero_smul, add_zero]

