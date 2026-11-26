import Mathlib
open scoped BigOperators
theorem AdvancedEncryption.WE.IPE.affine_key_offset {R M I : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Fintype I]
    (A : I → M) (G : M) (v w : I → R) (b : R) :
    (∑ i, v i • (A i + w i • G)) - ((∑ i, v i • A i) - b • G) =
      (b + ∑ i, v i * w i) • G := by sorry
