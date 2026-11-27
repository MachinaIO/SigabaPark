import Mathlib

theorem solution {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    (S A : Submodule K V → Submodule K V) (C : Set (V →ₗ[K] V))
    (sub : ∀ X, S X ≤ A X) (ext : ∀ X, X ≤ A X) (idem : ∀ X, A (A X) = A X)
    (fix : ∀ P ∈ C, ∀ X : Submodule K V, (∀ v ∈ X, P v = v) →
      ∀ v ∈ A X, P v = v) :
    (∀ X Z : Submodule K V, S X ≤ Z →
      ∃ P ∈ C, LinearMap.range P ≤ Z ∧ ∀ v ∈ X, P v = v) ↔
    (∀ X, A X = S X) ∧
      (∀ W : Submodule K V, A W = W →
        ∃ P ∈ C, LinearMap.range P ≤ W ∧ ∀ v ∈ W, P v = v) := by
  constructor
  · intro universal
    constructor
    · intro X
      refine le_antisymm ?_ (sub X)
      obtain ⟨P,hP,hr,hf⟩ := universal X (S X) le_rfl
      intro v hv
      exact hr ⟨v, fix P hP X hf v hv⟩
    · intro W hW
      exact universal W W (le_trans (sub W) hW.le)
  · rintro ⟨equal,splits⟩ X Z hXZ
    obtain ⟨P,hP,hr,hf⟩ := splits (A X) (idem X)
    refine ⟨P,hP,le_trans hr ((equal X) ▸ hXZ),?_⟩
    exact fun v hv => hf v (ext X hv)
