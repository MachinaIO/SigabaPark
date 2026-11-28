import Mathlib

theorem AdvancedEncryption.WE.PublicSlices.anf_attainable_span {K V X : Type} [Field K] [AddCommGroup V] [Module K V]
    (f : Finset X → V) (W : Submodule K V) :
    (∀ s : Finset X, (∑ t ∈ s.powerset, f t) ∈ W) ↔ (∀ t, f t ∈ W) := by
  sorry
