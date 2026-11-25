import SigabaNeoStd.Lattices.Homomorphic.Eval
import SigabaNeoStd.Lattices.SimNorm
import Mathlib.Tactic.Abel

open Matrix SigabaNeo.Lattices Cslib

theorem leaf_trapdoor {K : Type*} [CommRing K] {ℓ n m mW k : ℕ}
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


/-- The leaf trapdoor with its norm. Over `ℤ_q[X]/(X^N + 1)` (`N = 1`: `ℤ_q`), with binary
gadget decompositions, a bit attribute `w` and input trapdoors `R_j = R · T_W[j] − Σ_i w_i T_B[i,j]`
whose entries have norm at most `E`: if `φ(w) = 0`, then `A_φ − G = B R_φ − G` and every row of
`R_φ` has norm at most `errBound (k N) E φ`. -/
theorem solution {q N ℓ n m mW k : ℕ} [NeZero q]
    (Γ : GadgetMatrix (Negacyclic (ZMod q) N) (Fin n) (Fin k))
    (hΓ : ∀ A c c', cnorm (Γ.ginv A c c') ≤ 1)
    (B : Matrix (Fin n) (Fin m) (Negacyclic (ZMod q) N))
    (W : Fin ℓ → Matrix (Fin n) (Fin mW) (Negacyclic (ZMod q) N))
    (TB : Fin ℓ → Fin ℓ → Matrix (Fin m) (Fin k) (Negacyclic (ZMod q) N))
    (TW : Fin ℓ → Matrix (Fin mW) (Fin k) (Negacyclic (ZMod q) N))
    (h : ∀ i j, B * TB i j + W i * TW j = if i = j then Γ.G else 0)
    (w : Fin ℓ → Negacyclic (ZMod q) N) (hw : ∀ i, w i = 0 ∨ w i = 1)
    (R : Matrix (Fin m) (Fin mW) (Negacyclic (ZMod q) N)) (E : ℕ)
    (hE : ∀ j a c, cnorm ((R * TW j - ∑ i, w i • TB i j) a c) ≤ E)
    (φ : Circuit (Fin ℓ)) (hφ : φ.eval w = 0) :
    ∃ Rφ : Matrix (Fin m) (Fin k) (Negacyclic (ZMod q) N),
      evalMat Γ (fun j => ((∑ i, w i • W i) + B * R) * TW j) φ - Γ.G = B * Rφ - Γ.G ∧
      ∀ a, rnorm (rowOf Rφ a) ≤ errBound (k * N) E φ := by
  refine ⟨_, leaf_trapdoor Γ B W TB TW h w R φ hφ, fun a => ?_⟩
  simpa using rnorm_rowOf_evalSim_le Γ hΓ _ w hw (fun j => R * TW j - ∑ i, w i • TB i j) E hE φ a

