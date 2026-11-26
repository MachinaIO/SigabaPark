import SigabaNeoStd.Lattices.BoxSampler
import Definitions.Def_RingBoxesCopy
import SigabaNeoStd.Lattices.SimNorm
import SigabaNeoStd.Lattices.Homomorphic.Eval

open Matrix SigabaNeo.Lattices Cslib AdvancedEncryption.WE.RingBoxesCopy
open scoped ENNReal

open Classical in
/-- **The law of the leaf key is explicit**: for every trapdoor `T` of `[B | A]` covered by the
boxes, an output `(x, z)` has probability `1 / |Big|` if `x ∈ Small`, `z` is a decomposition and
`B x + A z = u`, and `0` otherwise. -/
theorem AdvancedEncryption.WE.Leaf.leafKey_apply_some {K : Type*} [CommRing K] [DecidableEq K] {n m k : ℕ}
    (G : Matrix (Fin n) (Fin k) K) (dec : (Fin n → K) → (Fin k → K))
    (hdec : ∀ y, G *ᵥ dec y = y) (B : Matrix (Fin n) (Fin m) K) (A : Matrix (Fin n) (Fin k) K)
    (T : (Fin k → K) → (Fin m → K)) (hT : ∀ z, B *ᵥ T z = (A + G) *ᵥ z)
    (Big Small : Finset (Fin m → K)) (hBig : Big.Nonempty)
    (hcov : ∀ x ∈ Small, ∀ y, x + T (dec (-y)) ∈ Big) (u : Fin n → K)
    (x : Fin m → K) (z : Fin k → K) :
    boxSample Big hBig Small (Matrix.mulVecLin B).toAddMonoidHom (fun y => dec (-y)) T u
        (some (x, z)) =
      if x ∈ Small ∧ (∃ y, dec y = z) ∧ B *ᵥ x + A *ᵥ z = u then (Big.card : ℝ≥0∞)⁻¹ else 0 := by sorry
