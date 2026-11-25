import SigabaNeoStd.Lattices.Homomorphic.Eval
import SigabaNeoStd.Lattices.SimNorm

open Matrix SigabaNeo.Lattices Cslib

theorem AdvancedEncryption.WE.Wee.leaf_trapdoor_norm {q N ℓ n m mW k : ℕ} [NeZero q]
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
      ∀ a, rnorm (rowOf Rφ a) ≤ errBound (k * N) E φ := by sorry
