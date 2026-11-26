import SigabaNeoStd.Lattices.LeftoverHash
import SigabaNeoStd.Lattices.BoxSampler
import SigabaNeoStd.Lattices.Homomorphic.Eval

open SigabaNeo.Lattices Cslib.Probability
open scoped ENNReal

open Matrix

theorem AdvancedEncryption.WE.LeafView.falseLeaf_message_mask {K : Type} [CommRing K] [Fintype K] [DecidableEq K]
    {n m mW k ℓ : ℕ} {Tt : Type} [NeZero m]
    (Γ : GadgetMatrix K (Fin n) (Fin k)) (dec : (Fin n → K) → Fin k → K)
    (hdec : ∀ y, Γ.G *ᵥ dec y = y) (Big Small : Finset (Fin m → K)) (hBig : Big.Nonempty)
    (u : Fin n → K) (φ : Circuit (Fin ℓ)) (w : Fin ℓ → K) (hφw : φ.eval w = 0)
    (S : Matrix (Fin n) (Fin m) K → PMF ((Fin ℓ → Matrix (Fin n) (Fin mW) K) × Tt))
    (good : Tt → Prop) [DecidablePred good]
    (TB : Tt → Fin ℓ → Fin ℓ → Matrix (Fin m) (Fin k) K)
    (TW : Tt → Fin ℓ → Matrix (Fin mW) (Fin k) K)
    (hblock : ∀ B, ∀ WT ∈ (S B).support, good WT.2 → ∀ i j,
      B * TB WT.2 i j + WT.1 i * TW WT.2 j = if i = j then Γ.G else 0)
    (hcov : ∀ B, ∀ WT ∈ (S B).support, good WT.2 → ∀ xs : Fin mW → Fin m → Bool,
      ∀ a ∈ Small, ∀ y, a + evalSim Γ (fun j ↦ ((∑ i, w i • WT.1 i) + B * (Matrix.of fun a c ↦ bitVal (xs c a) : Matrix (Fin m) (Fin mW) K)) * TW WT.2 j)
        w (fun j ↦ (Matrix.of fun a c ↦ bitVal (xs c a) : Matrix (Fin m) (Fin mW) K) * TW WT.2 j - ∑ i, w i • TB WT.2 i j) φ *ᵥ dec (-y) ∈ Big)
    (d₀ d₁ : Fin mW → K) :
    let ordinary : Matrix (Option (Fin n)) (Fin m) K → Matrix (Fin n) (Fin m) K := fun A i ↦ A (some i)
    let key := fun A xs ↦ (S (ordinary A)).bind fun WT ↦
      (if good WT.2 then boxSample Big hBig Small (Matrix.mulVecLin (ordinary A)).toAddMonoidHom
        (fun y ↦ dec (-y)) (fun z ↦ evalSim Γ (fun j ↦ ((∑ i, w i • WT.1 i) +
          ordinary A * (Matrix.of fun a c ↦ bitVal (xs c a) : Matrix (Fin m) (Fin mW) K)) * TW WT.2 j) w
          (fun j ↦ (Matrix.of fun a c ↦ bitVal (xs c a) : Matrix (Fin m) (Fin mW) K) * TW WT.2 j - ∑ i, w i • TB WT.2 i j) φ *ᵥ z) u
        else PMF.pure none).map fun k ↦ (WT,k)
    let run := fun (d : Fin mW → K) ↦
      (PMF.uniformOfFintype (Matrix (Option (Fin n)) (Fin m) K)).bind fun A ↦
        (Cslib.Probability.PMF.pi fun _ : Fin mW ↦ PMF.uniformOfFintype (Fin m → Bool)).bind fun xs ↦
          (key A xs).map fun k ↦ (A, fun i j ↦ binaryHash A (xs i) (some j), k,
            fun i ↦ d i + binaryHash A (xs i) none)
    let ε := ENNReal.ofReal ((mW : ℝ) * (Real.sqrt
      ((Fintype.card K : ℝ) ^ (n+1) * (2 ^ m : ℝ)⁻¹) / 2))
    CloseTo (run d₀) (run d₁) (ε+ε) := by
  sorry
