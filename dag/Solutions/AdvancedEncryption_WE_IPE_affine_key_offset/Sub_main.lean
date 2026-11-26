import Mathlib
open scoped BigOperators
theorem solution {R M I : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Fintype I]
    (A : I → M) (G : M) (v w : I → R) (b : R) :
    (∑ i, v i • (A i + w i • G)) - ((∑ i, v i • A i) - b • G) =
      (b + ∑ i, v i * w i) • G := by
  simp only [smul_add, smul_smul, Finset.sum_add_distrib, add_smul, Finset.sum_smul]
  abel
