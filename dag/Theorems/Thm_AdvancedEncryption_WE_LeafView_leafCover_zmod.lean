import SigabaNeoStd.Lattices.BoxSampler
import SigabaNeoStd.Lattices.LeftoverHash
import SigabaNeoStd.Lattices.Homomorphic.Eval
import CslibFrontier.Probability.Product
import SigabaNeoStd.Lattices.Boxes
import SigabaNeoStd.Lattices.Homomorphic.NoiseBound

open Matrix SigabaNeo.Lattices Cslib Cslib.Probability
open scoped ENNReal

/-- **Coverage over `ℤ_q`**: with gadget decompositions and `dec` of entries at most `1`, bit
inputs `x` and input trapdoors `Wm` with entries at most `E`, the simulation trapdoor
`evalSim Γ A x Wm φ` keeps `ball s` in the big box of `Bb` bits when
`s + k · errBound k E φ ≤ 2^{Bb−1} − 1`. -/
theorem AdvancedEncryption.WE.LeafView.leafCover_zmod {q n m k ℓ : ℕ} [NeZero q] (Γ : GadgetMatrix (ZMod q) (Fin n) (Fin k))
    (hΓ : ∀ A c c', zabs (Γ.ginv A c c') ≤ 1) (dec : (Fin n → ZMod q) → (Fin k → ZMod q))
    (hdecN : ∀ y c, zabs (dec y c) ≤ 1) (A : Fin ℓ → Matrix (Fin n) (Fin k) (ZMod q))
    (x : Fin ℓ → ZMod q) (hx : ∀ j, x j = 0 ∨ x j = 1)
    (Wm : Fin ℓ → Matrix (Fin m) (Fin k) (ZMod q)) (E : ℕ) (hW : ∀ j a c, zabs (Wm j a c) ≤ E)
    (φ : Circuit (Fin ℓ)) (Bb s : ℕ) (hB : 2 ^ Bb ≤ q) (hB1 : 1 ≤ Bb)
    (hs : s + k * errBound k E φ ≤ 2 ^ (Bb - 1) - 1) :
    ∀ v ∈ (ball q s : Finset (Fin m → ZMod q)), ∀ y,
      v + evalSim Γ A x Wm φ *ᵥ dec (-y) ∈ (bigBox Bb hB : Finset (Fin m → ZMod q)) := by sorry
