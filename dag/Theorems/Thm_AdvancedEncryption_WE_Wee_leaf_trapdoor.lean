import SigabaNeoStd.Lattices.Homomorphic.Eval

open Matrix SigabaNeo.Lattices

theorem AdvancedEncryption.WE.Wee.leaf_trapdoor {K : Type*} [CommRing K] {ℓ n m mW k : ℕ}
    (Γ : GadgetMatrix K (Fin n) (Fin k))
    (B : Matrix (Fin n) (Fin m) K) (W : Fin ℓ → Matrix (Fin n) (Fin mW) K)
    (TB : Fin ℓ → Fin ℓ → Matrix (Fin m) (Fin k) K) (TW : Fin ℓ → Matrix (Fin mW) (Fin k) K)
    (h : ∀ i j, B * TB i j + W i * TW j = if i = j then Γ.G else 0)
    (w : Fin ℓ → K) (R : Matrix (Fin m) (Fin mW) K) (φ : Circuit (Fin ℓ))
    (hφ : φ.eval w = 0) :
    evalMat Γ (fun j => ((∑ i, w i • W i) + B * R) * TW j) φ - Γ.G =
      B * evalSim Γ (fun j => ((∑ i, w i • W i) + B * R) * TW j) w
        (fun j => R * TW j - ∑ i, w i • TB i j) φ - Γ.G := by sorry
