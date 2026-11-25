import SigabaNeoStd.Lattices.BoxSampler
import SigabaNeoStd.Lattices.LeftoverHash
import SigabaNeoStd.Lattices.Homomorphic.Eval
import CslibFrontier.Probability.Product
import SigabaNeoStd.Lattices.Boxes
import SigabaNeoStd.Lattices.Homomorphic.NoiseBound

open Matrix SigabaNeo.Lattices Cslib Cslib.Probability
open scoped ENNReal

/-- **The leaf view is simulated up to the leftover hash lemma, with no trapdoor for `B`.**

Real (attribute `0`): `B` uniform, `R` binary, `(W, T) ← S(B)`, `A = B R`; if the public check
`good T` passes, the leaf key is one try of box rejection for `[B | A_φ − G]` with the
simulation trapdoor `R_φ^{(0)}` (`φ(0) = 0`), otherwise `⊥`.
Simulated (attribute `w` with `φ(w) = 0`): `A = Σ w_i W_i + B R` and the trapdoor
`R_φ^{(w)}` built from `R T_W[j] − Σ_i w_i T_B[i,j]`.
The two views `(B, W, T, A, key)` are within twice the leftover-hash bound. -/
theorem AdvancedEncryption.WE.LeafView.leafView_close {K : Type} [CommRing K] [Fintype K] [DecidableEq K] {n m mW k ℓ : ℕ} {Tt : Type} (Γ : GadgetMatrix K (Fin n) (Fin k)) (dec : (Fin n → K) → (Fin k → K))
    (hdec : ∀ y, Γ.G *ᵥ dec y = y) (Big Small : Finset (Fin m → K)) (hBig : Big.Nonempty)
    (u : Fin n → K) (φ : Circuit (Fin ℓ)) (w : Fin ℓ → K) (hφ0 : φ.eval (0 : Fin ℓ → K) = 0)
    (hφw : φ.eval w = 0) [NeZero m]
    (S : Matrix (Fin n) (Fin m) K → PMF ((Fin ℓ → Matrix (Fin n) (Fin mW) K) × Tt))
    (good : Tt → Prop) [DecidablePred good]
    (TB : Tt → Fin ℓ → Fin ℓ → Matrix (Fin m) (Fin k) K) (TW : Tt → Fin ℓ → Matrix (Fin mW) (Fin k) K)
    (hblock : ∀ B, ∀ WT ∈ (S B).support, good WT.2 → ∀ i j,
      B * TB WT.2 i j + WT.1 i * TW WT.2 j = if i = j then Γ.G else 0)
    (hcov : ∀ B, ∀ WT ∈ (S B).support, good WT.2 → ∀ R : Matrix (Fin m) (Fin mW) K,
      (∀ a c, R a c = 0 ∨ R a c = 1) →
      (∀ x ∈ Small, ∀ y, x + evalSim Γ (fun j => (B * R) * TW WT.2 j) 0
          (fun j => R * TW WT.2 j) φ *ᵥ dec (-y) ∈ Big) ∧
      (∀ x ∈ Small, ∀ y, x + evalSim Γ (fun j => ((∑ i, w i • WT.1 i) + B * R) * TW WT.2 j) w
          (fun j => R * TW WT.2 j - ∑ i, w i • TB WT.2 i j) φ *ᵥ dec (-y) ∈ Big)) :
    CloseTo
      ((PMF.uniformOfFintype (Matrix (Fin n) (Fin m) K)).bind fun B =>
        (Cslib.Probability.PMF.pi fun _ : Fin mW => PMF.uniformOfFintype (Fin m → Bool)).bind
          fun xs => (S B).bind fun WT =>
            (if good WT.2 then
              boxSample Big hBig Small (Matrix.mulVecLin B).toAddMonoidHom (fun y => dec (-y))
                (fun z => evalSim Γ (fun j => (B * (Matrix.of fun a c => bitVal (xs c a) : Matrix (Fin m) (Fin mW) K)) * TW WT.2 j) 0
                  (fun j => (Matrix.of fun a c => bitVal (xs c a) : Matrix (Fin m) (Fin mW) K) * TW WT.2 j) φ *ᵥ z) u
            else PMF.pure none).map fun key => (B, WT, B * (Matrix.of fun a c => bitVal (xs c a) : Matrix (Fin m) (Fin mW) K), key))
      ((PMF.uniformOfFintype (Matrix (Fin n) (Fin m) K)).bind fun B =>
        (Cslib.Probability.PMF.pi fun _ : Fin mW => PMF.uniformOfFintype (Fin m → Bool)).bind
          fun xs => (S B).bind fun WT =>
            (if good WT.2 then
              boxSample Big hBig Small (Matrix.mulVecLin B).toAddMonoidHom (fun y => dec (-y))
                (fun z => evalSim Γ (fun j => ((∑ i, w i • WT.1 i) + B * (Matrix.of fun a c => bitVal (xs c a) : Matrix (Fin m) (Fin mW) K)) * TW WT.2 j) w
                  (fun j => (Matrix.of fun a c => bitVal (xs c a) : Matrix (Fin m) (Fin mW) K) * TW WT.2 j - ∑ i, w i • TB WT.2 i j) φ *ᵥ z) u
            else PMF.pure none).map fun key => (B, WT, (∑ i, w i • WT.1 i) + B * (Matrix.of fun a c => bitVal (xs c a) : Matrix (Fin m) (Fin mW) K), key))
      (ENNReal.ofReal (mW * (Real.sqrt ((Fintype.card K : ℝ) ^ n * (2 ^ m : ℝ)⁻¹) / 2)) +
        ENNReal.ofReal (mW * (Real.sqrt ((Fintype.card K : ℝ) ^ n * (2 ^ m : ℝ)⁻¹) / 2))) := by sorry
