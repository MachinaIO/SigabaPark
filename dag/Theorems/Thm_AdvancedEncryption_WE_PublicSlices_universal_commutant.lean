import Mathlib

theorem AdvancedEncryption.WE.PublicSlices.universal_commutant {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    (S A : Submodule K V → Submodule K V) (C : Set (V →ₗ[K] V))
    (sub : ∀ X, S X ≤ A X) (ext : ∀ X, X ≤ A X) (idem : ∀ X, A (A X) = A X)
    (fix : ∀ P ∈ C, ∀ X : Submodule K V, (∀ v ∈ X, P v = v) →
      ∀ v ∈ A X, P v = v) :
    (∀ X Z : Submodule K V, S X ≤ Z →
      ∃ P ∈ C, LinearMap.range P ≤ Z ∧ ∀ v ∈ X, P v = v) ↔
    (∀ X, A X = S X) ∧
      (∀ W : Submodule K V, A W = W →
        ∃ P ∈ C, LinearMap.range P ≤ W ∧ ∀ v ∈ W, P v = v) := by
  sorry
