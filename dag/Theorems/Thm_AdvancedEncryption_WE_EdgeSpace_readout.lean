import Mathlib

open scoped BigOperators

theorem AdvancedEncryption.WE.EdgeSpace.readout {ι V K : Type} [Fintype ι] [AddCommGroup V] [AddCommGroup K]
    {W : ι → Type} [∀ i, AddCommGroup (W i)]
    (r : (i : ι) → V →+ W i) (read : (i : ι) → W i →+ K) (ell : V →+ K)
    (hf : ∀ i v, read i (r i v) = ell v) (a : ι → V) (u : V) (hu : ∑ i, a i = u) :
    ∑ i, read i (r i (a i)) = ell u := by sorry
