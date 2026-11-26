import SigabaNeoStd.Lattices.BoxSampler
import SigabaNeoStd.Lattices.LeftoverHash
import SigabaNeoStd.Lattices.Homomorphic.Eval
import CslibFrontier.Probability.Product
import SigabaNeoStd.Lattices.Boxes
import SigabaNeoStd.Lattices.Homomorphic.NoiseBound
import Definitions.Def_WE_EncryptorLeafSetup
import Theorems.Thm_AdvancedEncryption_WE_LeafView_encryptorSetup_close
import Theorems.Thm_AdvancedEncryption_WE_LeafView_leafView_close_succinct

open Matrix SigabaNeo.Lattices Cslib Cslib.Probability AdvancedEncryption.WE.Assumptions.SuccinctLWE
  AdvancedEncryption.WE.EncryptorSetup
open scoped ENNReal

namespace EncLeafAux

open Cslib.Probability

theorem view_eq {β γ δ X : Type} (μB : PMF β) (μx : PMF γ) (S : β → PMF δ)
    (K : β → γ → δ → PMF X) :
    (μB.bind fun B => μx.bind fun xs => (S B).bind fun WT => K B xs WT) =
      (μB.bind fun B => (S B).map fun WT => (B, WT)).bind fun BW =>
        μx.bind fun xs => K BW.1 xs BW.2 := by
  rw [PMF.bind_bind]
  congr 1; funext B
  rw [PMF.bind_map, PMF.bind_comm]
  rfl

theorem view_close {β γ δ X : Type} (μB : PMF β) (μx : PMF γ) (S S' : β → PMF δ)
    (K : β → γ → δ → PMF X) {ε : ℝ≥0∞}
    (h : CloseTo (μB.bind fun B => (S B).map fun WT => (B, WT))
      (μB.bind fun B => (S' B).map fun WT => (B, WT)) ε) :
    CloseTo (μB.bind fun B => μx.bind fun xs => (S B).bind fun WT => K B xs WT)
      (μB.bind fun B => μx.bind fun xs => (S' B).bind fun WT => K B xs WT) ε := by
  rw [view_eq, view_eq]
  exact h.bind_left _

theorem joint_enc (p : Params) (mb : ℕ) (hm : mb + p.ℓ * p.n * p.k = p.m)
    (hσ : (0 : ℝ) < p.σ) :
    ((PMF.uniformOfFintype (Matrix (Fin p.n) (Fin p.m) (ZMod p.q))).bind fun B =>
      (leafSetupEnc p mb hm hσ B).map fun WT => (B, WT)) =
      (encLaw p mb hm hσ).map fun x => (x.1, fun i r c => x.2.1 (finProdFinEquiv (i, r)) c, x.2.2) := by
  unfold leafSetupEnc encLaw
  simp only [PMF.map_bind, PMF.map_comp]
  rfl

theorem joint_chal (p : Params) :
    ((PMF.uniformOfFintype (Matrix (Fin p.n) (Fin p.m) (ZMod p.q))).bind fun B =>
      (leafSetup p B).map fun WT => (B, WT)) =
      (chalLaw p).map fun x => (x.1, fun i r c => x.2.1 (finProdFinEquiv (i, r)) c, x.2.2) := by
  unfold leafSetup chalLaw
  simp only [PMF.map_bind, PMF.map_comp]
  rfl

end EncLeafAux

open Classical in
/-- **The leaf view over the WE encryptor's own setup.** The real leaf view (attribute `0`) and
the simulated view (attribute `w`), each with the encryptor's `(W, T)` (`leafSetupEnc`: `W` with a
gadget trapdoor, `T` by flooding, no trapdoor for `B`), are within twice the bound of
`encryptorSetup_close` plus twice the leftover-hash bound of `leafView_close_succinct`. -/
theorem solution (p : Params) [Fact p.q.Prime]
    [NeZero p.m] (mb : ℕ) (hm : mb + p.ℓ * p.n * p.k = p.m)
    (hmb : 0 < mb) (hσ : (0 : ℝ) < p.σ) (hσ1 : (1 : ℝ) ≤ p.σ) (h2 : 2 * (p.σ : ℝ) ≤ p.q)
    (hexp : 3 * Real.exp (-(Real.pi * (p.σ : ℝ) ^ 2)) * p.m ≤ 1 / 2)
    (hrad : (p.σ : ℝ) * Real.sqrt (p.ℓ * p.m + p.m : ℕ) + (p.ℓ * p.n * p.k : ℕ) ≤
      (p.σ : ℝ) * (p.ℓ * p.m + p.m : ℕ))
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
          fun xs => (leafSetupEnc p mb hm hσ B).bind fun WT =>
            (if leafGood ET WT.2 then
              boxSample (bigBox Bb hB) hBig (ball p.q s)
                (Matrix.mulVecLin B).toAddMonoidHom (fun y => dec (-y))
                (fun z => evalSim Γ (fun j => (B * (Matrix.of fun a c => bitVal (xs c a) : Matrix (Fin p.m) (Fin p.m) (ZMod p.q))) * leafTW WT.2 j) 0
                  (fun j => (Matrix.of fun a c => bitVal (xs c a) : Matrix (Fin p.m) (Fin p.m) (ZMod p.q)) * leafTW WT.2 j) φ *ᵥ z) u
            else PMF.pure none).map fun key => (B, WT, B * (Matrix.of fun a c => bitVal (xs c a) : Matrix (Fin p.m) (Fin p.m) (ZMod p.q)), key))
      ((PMF.uniformOfFintype (Matrix (Fin p.n) (Fin p.m) (ZMod p.q))).bind fun B =>
        (Cslib.Probability.PMF.pi fun _ : Fin p.m => PMF.uniformOfFintype (Fin p.m → Bool)).bind
          fun xs => (leafSetupEnc p mb hm hσ B).bind fun WT =>
            (if leafGood ET WT.2 then
              boxSample (bigBox Bb hB) hBig (ball p.q s)
                (Matrix.mulVecLin B).toAddMonoidHom (fun y => dec (-y))
                (fun z => evalSim Γ (fun j => ((∑ i, w i • WT.1 i) + B * (Matrix.of fun a c => bitVal (xs c a) : Matrix (Fin p.m) (Fin p.m) (ZMod p.q))) * leafTW WT.2 j) w
                  (fun j => (Matrix.of fun a c => bitVal (xs c a) : Matrix (Fin p.m) (Fin p.m) (ZMod p.q)) * leafTW WT.2 j - ∑ i, w i • leafTB WT.2 i j) φ *ᵥ z) u
            else PMF.pure none).map fun key => (B, WT, (∑ i, w i • WT.1 i) + B * (Matrix.of fun a c => bitVal (xs c a) : Matrix (Fin p.m) (Fin p.m) (ZMod p.q)), key))
      (2 * ((p.ℓ * (p.n * p.k) : ℕ) * (ENNReal.ofReal (2 * (Real.pi * (p.ℓ * p.m + p.m : ℕ) *
          (((p.ℓ * p.n * p.k : ℕ) : ℝ) ^ 2 + 2 * ((p.σ : ℝ) * (p.ℓ * p.m + p.m : ℕ)) *
            (p.ℓ * p.n * p.k : ℕ)) / (p.σ : ℝ) ^ 2)) +
        ((p.ℓ * p.m + p.m : ℕ) : ℝ≥0∞) * ENNReal.ofReal (6 * (1 / 4) ^ (p.ℓ * p.m + p.m)) +
        ENNReal.ofReal (3 * 2 ^ (p.ℓ * p.m + p.m) * (1 / 4) ^ ((p.ℓ * p.m + p.m) ^ 2))) +
      ENNReal.ofReal (4 * (p.ℓ + 1) * (12 * Real.exp (-(Real.pi * (p.σ : ℝ) ^ 2)) * p.m +
          ((p.q : ℝ) ^ p.n + (p.q : ℝ) ^ (p.ℓ * p.n)) * (4 / (p.σ : ℝ)) ^ p.m)) +
      2 * ENNReal.ofReal ((p.ℓ * p.n * p.k : ℕ) *
        (Real.sqrt ((p.q : ℝ) ^ (p.ℓ * p.n) * (2 ^ mb : ℝ)⁻¹) / 2))) +
        (ENNReal.ofReal (p.m * (Real.sqrt ((p.q : ℝ) ^ p.n * (2 ^ p.m : ℝ)⁻¹) / 2)) +
        ENNReal.ofReal (p.m * (Real.sqrt ((p.q : ℝ) ^ p.n * (2 ^ p.m : ℝ)⁻¹) / 2)))) := by
  have hset := AdvancedEncryption.WE.LeafView.encryptorSetup_close p mb hm hmb hσ hσ1 h2 hexp hrad
  have hleaf := AdvancedEncryption.WE.LeafView.leafView_close_succinct p Γ hΓG hΓ dec hdec hdecN
    Bb s hB hB1 hBig u φ w hw hφ0 hφw ET hs
  have hj1 := hset.map fun x => (x.1, fun i r c => x.2.1 (finProdFinEquiv (i, r)) c, x.2.2)
  have hj2 := hset.symm.map fun x => (x.1, fun i r c => x.2.1 (finProdFinEquiv (i, r)) c, x.2.2)
  rw [← EncLeafAux.joint_enc, ← EncLeafAux.joint_chal] at hj1 hj2
  refine (((EncLeafAux.view_close _ _ _ _ _ hj1).trans hleaf).trans
    (EncLeafAux.view_close _ _ _ _ _ hj2)).mono (le_of_eq ?_)
  ring
