import Mathlib

theorem AdvancedEncryption.WE.OddFault.NormalizedView {R ι : Type*} [CommRing R] [Fintype ι]
    (a t e m : R) (w k : ι → R) (hw : ∑ i, w i = 1) :
    ∑ i, w i * (a * (t + k i) + e + m) = a * (t + ∑ i, w i * k i) + e + m := by sorry
