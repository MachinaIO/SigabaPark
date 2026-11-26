import Definitions.Def_RingBoxesCopy
import SigabaNeoStd.Lattices.BoxSampler

open SigabaNeo.Lattices AdvancedEncryption.WE.RingBoxesCopy
open scoped ENNReal

theorem AdvancedEncryption.WE.LeafView.zmodBox_abort_le {q m : ℕ} [NeZero q] {Y Z : Type} [AddCommGroup Y]
    (F : (Fin m → ZMod q) →+ Y) (dec : Y → Z) (T : Z → Fin m → ZMod q) (u : Y)
    (Bb s τ κ : ℕ) (hB : 2 ^ Bb ≤ q) (hB1 : 1 ≤ Bb)
    (hBig : (bigBox Bb hB : Finset (Fin m → ZMod q)).Nonempty)
    (hs : 2 ^ (Bb - 1) - 1 - τ ≤ s) (hτ : 4 * τ + 1 ≤ 2 ^ Bb)
    (hκ : m * (4 * τ + 1) * 2 ^ κ ≤ 2 ^ Bb)
    (hshift : ∀ y i, zabs (T (dec y) i) ≤ τ) :
    boxSample (bigBox Bb hB) hBig (ball q s) F dec T u none ≤ ((2 : ℝ≥0∞) ^ κ)⁻¹ := by
  sorry
