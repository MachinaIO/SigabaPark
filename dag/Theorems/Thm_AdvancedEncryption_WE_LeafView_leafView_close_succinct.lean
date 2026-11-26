import SigabaNeoStd.Lattices.BoxSampler
import SigabaNeoStd.Lattices.LeftoverHash
import SigabaNeoStd.Lattices.Homomorphic.Eval
import CslibFrontier.Probability.Product
import SigabaNeoStd.Lattices.Boxes
import SigabaNeoStd.Lattices.Homomorphic.NoiseBound
import Definitions.Def_WE_EncryptorSetup

open Matrix SigabaNeo.Lattices Cslib Cslib.Probability AdvancedEncryption.WE.Assumptions.SuccinctLWE
  AdvancedEncryption.WE.EncryptorSetup
open scoped ENNReal

open Classical in
/-- **The leaf view with `Def_SuccinctLWE`'s own setup.** `leafView_close_zmod` instantiated with the
setup kernel `B ↦ (W ← uniform, T ← trapdoorLaw p B W)` (`W` split into its `ℓ` row blocks), the
public check "`T ≠ none` and its entries are at most `E_T`", the blocks `T_B[i,j]`, `T_W[j]` of
`T`, and a gadget `Γ` with `Γ.G = G` of `Def_SuccinctLWE` (one exists: `succ_gadget_exists`). The
block identity `B T_B[i,j] + W_i T_W[j] = δ_ij G` then holds on the support, so the real view
(attribute `0`) and the simulated view (attribute `w`) are within `m √(q^n / 2^m)`. -/
theorem AdvancedEncryption.WE.LeafView.leafView_close_succinct (p : Params) [NeZero p.m]
    (Γ : GadgetMatrix (ZMod p.q) (Fin p.n) (Fin (p.n * p.k)))
    (hΓG : Γ.G = AdvancedEncryption.WE.Assumptions.SuccinctLWE.gadget p.n p.k p.q)
    (hΓ : ∀ A c c', zabs (Γ.ginv A c c') ≤ 1) (dec : (Fin p.n → ZMod p.q) → (Fin (p.n * p.k) → ZMod p.q))
    (hdec : ∀ y, Γ.G *ᵥ dec y = y) (hdecN : ∀ y c, zabs (dec y c) ≤ 1)
    (Bb s : ℕ) (hB : 2 ^ Bb ≤ p.q) (hB1 : 1 ≤ Bb)
    (hBig : (bigBox Bb hB : Finset (Fin p.m → ZMod p.q)).Nonempty)
    (u : Fin p.n → ZMod p.q) (φ : Circuit (Fin p.ℓ)) (w : Fin p.ℓ → ZMod p.q) (hw : ∀ i, w i = 0 ∨ w i = 1)
    (hφ0 : φ.eval (0 : Fin p.ℓ → ZMod p.q) = 0) (hφw : φ.eval w = 0) (ET : ℕ)
    (hs : s + p.n * p.k * errBound (p.n * p.k) ((p.m + p.ℓ) * ET) φ ≤ 2 ^ (Bb - 1) - 1) :
    CloseTo
      ((PMF.uniformOfFintype (Matrix (Fin p.n) (Fin p.m) (ZMod p.q))).bind fun B =>
        (Cslib.Probability.PMF.pi fun _ : Fin p.m => PMF.uniformOfFintype (Fin p.m → Bool)).bind
          fun xs => (leafSetup p B).bind fun WT =>
            (if leafGood ET WT.2 then
              boxSample (bigBox Bb hB) hBig (ball p.q s)
                (Matrix.mulVecLin B).toAddMonoidHom (fun y => dec (-y))
                (fun z => evalSim Γ (fun j => (B * (Matrix.of fun a c => bitVal (xs c a) : Matrix (Fin p.m) (Fin p.m) (ZMod p.q))) * leafTW WT.2 j) 0
                  (fun j => (Matrix.of fun a c => bitVal (xs c a) : Matrix (Fin p.m) (Fin p.m) (ZMod p.q)) * leafTW WT.2 j) φ *ᵥ z) u
            else PMF.pure none).map fun key => (B, WT, B * (Matrix.of fun a c => bitVal (xs c a) : Matrix (Fin p.m) (Fin p.m) (ZMod p.q)), key))
      ((PMF.uniformOfFintype (Matrix (Fin p.n) (Fin p.m) (ZMod p.q))).bind fun B =>
        (Cslib.Probability.PMF.pi fun _ : Fin p.m => PMF.uniformOfFintype (Fin p.m → Bool)).bind
          fun xs => (leafSetup p B).bind fun WT =>
            (if leafGood ET WT.2 then
              boxSample (bigBox Bb hB) hBig (ball p.q s)
                (Matrix.mulVecLin B).toAddMonoidHom (fun y => dec (-y))
                (fun z => evalSim Γ (fun j => ((∑ i, w i • WT.1 i) + B * (Matrix.of fun a c => bitVal (xs c a) : Matrix (Fin p.m) (Fin p.m) (ZMod p.q))) * leafTW WT.2 j) w
                  (fun j => (Matrix.of fun a c => bitVal (xs c a) : Matrix (Fin p.m) (Fin p.m) (ZMod p.q)) * leafTW WT.2 j - ∑ i, w i • leafTB WT.2 i j) φ *ᵥ z) u
            else PMF.pure none).map fun key => (B, WT, (∑ i, w i • WT.1 i) + B * (Matrix.of fun a c => bitVal (xs c a) : Matrix (Fin p.m) (Fin p.m) (ZMod p.q)), key))
      (ENNReal.ofReal (p.m * (Real.sqrt ((p.q : ℝ) ^ p.n * (2 ^ p.m : ℝ)⁻¹) / 2)) +
        ENNReal.ofReal (p.m * (Real.sqrt ((p.q : ℝ) ^ p.n * (2 ^ p.m : ℝ)⁻¹) / 2))) := by sorry
