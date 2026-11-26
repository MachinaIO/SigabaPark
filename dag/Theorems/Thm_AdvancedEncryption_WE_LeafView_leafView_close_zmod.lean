import SigabaNeoStd.Lattices.BoxSampler
import SigabaNeoStd.Lattices.LeftoverHash
import SigabaNeoStd.Lattices.Homomorphic.Eval
import CslibFrontier.Probability.Product
import SigabaNeoStd.Lattices.Boxes
import SigabaNeoStd.Lattices.Homomorphic.NoiseBound

open Matrix SigabaNeo.Lattices Cslib Cslib.Probability
open scoped ENNReal

/-- **The leaf view over `ℤ_q` with norm-checked trapdoors.** The public check `good T` bounds the
entries of `T_B`, `T_W` by `E_T`; with bit attributes, `φ(0) = φ(w) = 0`, small box `ball s` and
big box of `Bb` bits with `s + k · errBound k ((m_W + ℓ) E_T) φ ≤ 2^{Bb−1} − 1`, the real view
(attribute `0`, no trapdoor for `B`) and the simulated view (attribute `w`) are within twice the
leftover-hash bound `m_W √(q^n / 2^m) / 2`. -/
theorem AdvancedEncryption.WE.LeafView.leafView_close_zmod {q n m mW k ℓ : ℕ} [NeZero q] {Tt : Type} (Γ : GadgetMatrix (ZMod q) (Fin n) (Fin k))
    (hΓ : ∀ A c c', zabs (Γ.ginv A c c') ≤ 1) (dec : (Fin n → ZMod q) → (Fin k → ZMod q))
    (hdec : ∀ y, Γ.G *ᵥ dec y = y) (hdecN : ∀ y c, zabs (dec y c) ≤ 1)
    (Bb s : ℕ) (hB : 2 ^ Bb ≤ q) (hB1 : 1 ≤ Bb)
    (hBig : (bigBox Bb hB : Finset (Fin m → ZMod q)).Nonempty)
    (u : Fin n → ZMod q) (φ : Circuit (Fin ℓ)) (w : Fin ℓ → ZMod q) (hw : ∀ i, w i = 0 ∨ w i = 1)
    (hφ0 : φ.eval (0 : Fin ℓ → ZMod q) = 0) (hφw : φ.eval w = 0) [NeZero m]
    (S : Matrix (Fin n) (Fin m) (ZMod q) → PMF ((Fin ℓ → Matrix (Fin n) (Fin mW) (ZMod q)) × Tt))
    (good : Tt → Prop) [DecidablePred good]
    (TB : Tt → Fin ℓ → Fin ℓ → Matrix (Fin m) (Fin k) (ZMod q))
    (TW : Tt → Fin ℓ → Matrix (Fin mW) (Fin k) (ZMod q))
    (hblock : ∀ B, ∀ WT ∈ (S B).support, good WT.2 → ∀ i j,
      B * TB WT.2 i j + WT.1 i * TW WT.2 j = if i = j then Γ.G else 0)
    (ET : ℕ) (hgood : ∀ T, good T →
      (∀ i j a c, zabs (TB T i j a c) ≤ ET) ∧ ∀ j a c, zabs (TW T j a c) ≤ ET)
    (hs : s + k * errBound k ((mW + ℓ) * ET) φ ≤ 2 ^ (Bb - 1) - 1) :
    CloseTo
      ((PMF.uniformOfFintype (Matrix (Fin n) (Fin m) (ZMod q))).bind fun B =>
        (Cslib.Probability.PMF.pi fun _ : Fin mW => PMF.uniformOfFintype (Fin m → Bool)).bind
          fun xs => (S B).bind fun WT =>
            (if good WT.2 then
              boxSample (bigBox Bb hB) hBig (ball q s)
                (Matrix.mulVecLin B).toAddMonoidHom (fun y => dec (-y))
                (fun z => evalSim Γ (fun j => (B * (Matrix.of fun a c => bitVal (xs c a) : Matrix (Fin m) (Fin mW) (ZMod q))) * TW WT.2 j) 0
                  (fun j => (Matrix.of fun a c => bitVal (xs c a) : Matrix (Fin m) (Fin mW) (ZMod q)) * TW WT.2 j) φ *ᵥ z) u
            else PMF.pure none).map fun key => (B, WT, B * (Matrix.of fun a c => bitVal (xs c a) : Matrix (Fin m) (Fin mW) (ZMod q)), key))
      ((PMF.uniformOfFintype (Matrix (Fin n) (Fin m) (ZMod q))).bind fun B =>
        (Cslib.Probability.PMF.pi fun _ : Fin mW => PMF.uniformOfFintype (Fin m → Bool)).bind
          fun xs => (S B).bind fun WT =>
            (if good WT.2 then
              boxSample (bigBox Bb hB) hBig (ball q s)
                (Matrix.mulVecLin B).toAddMonoidHom (fun y => dec (-y))
                (fun z => evalSim Γ (fun j => ((∑ i, w i • WT.1 i) + B * (Matrix.of fun a c => bitVal (xs c a) : Matrix (Fin m) (Fin mW) (ZMod q))) * TW WT.2 j) w
                  (fun j => (Matrix.of fun a c => bitVal (xs c a) : Matrix (Fin m) (Fin mW) (ZMod q)) * TW WT.2 j - ∑ i, w i • TB WT.2 i j) φ *ᵥ z) u
            else PMF.pure none).map fun key => (B, WT, (∑ i, w i • WT.1 i) + B * (Matrix.of fun a c => bitVal (xs c a) : Matrix (Fin m) (Fin mW) (ZMod q)), key))
      (ENNReal.ofReal (mW * (Real.sqrt ((q : ℝ) ^ n * (2 ^ m : ℝ)⁻¹) / 2)) +
        ENNReal.ofReal (mW * (Real.sqrt ((q : ℝ) ^ n * (2 ^ m : ℝ)⁻¹) / 2))) := by sorry
