import SigabaNeoStd.Lattices.BoxSampler
import Definitions.Def_RingBoxesCopy
import SigabaNeoStd.Lattices.SimNorm
import SigabaNeoStd.Lattices.Homomorphic.Eval

open Matrix SigabaNeo.Lattices Cslib AdvancedEncryption.WE.RingBoxesCopy
open scoped ENNReal

/-- **Exact simulation of the leaf key.** If `B Tm = G` and `A = B R − G`, the leaf-key law with
the real trapdoor `Tm · G⁻¹(A + G)` of `B` equals the law with the `−G` trapdoor `R`, provided
the big box covers both shifts. -/
theorem AdvancedEncryption.WE.Leaf.leafKey_real_eq_sim {K : Type*} [CommRing K] [DecidableEq K] {n m k : ℕ}
    (Γ : GadgetMatrix K (Fin n) (Fin k))
    (dec : (Fin n → K) → (Fin k → K)) (hdec : ∀ y, Γ.G *ᵥ dec y = y)
    (B : Matrix (Fin n) (Fin m) K) (Tm : Matrix (Fin m) (Fin k) K) (hTm : B * Tm = Γ.G)
    (R : Matrix (Fin m) (Fin k) K) (A : Matrix (Fin n) (Fin k) K) (hA : A = B * R - Γ.G)
    (Big Small : Finset (Fin m → K)) (hBig : Big.Nonempty)
    (hcov : ∀ x ∈ Small, ∀ y, x + (Tm * Γ.ginv (A + Γ.G)) *ᵥ dec (-y) ∈ Big)
    (hcov' : ∀ x ∈ Small, ∀ y, x + R *ᵥ dec (-y) ∈ Big) (u : Fin n → K) :
    boxSample Big hBig Small (Matrix.mulVecLin B).toAddMonoidHom (fun y => dec (-y))
        (fun z => (Tm * Γ.ginv (A + Γ.G)) *ᵥ z) u =
      boxSample Big hBig Small (Matrix.mulVecLin B).toAddMonoidHom (fun y => dec (-y))
        (fun z => R *ᵥ z) u := by sorry
