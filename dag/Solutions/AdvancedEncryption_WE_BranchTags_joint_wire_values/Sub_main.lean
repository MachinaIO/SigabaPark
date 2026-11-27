import Mathlib.Data.Set.Operations

theorem solution
    {I V A B : Type*} (S T : Set I) (f : (I → V) → A) (g : (I → V) → B)
    (hf : ∀ u v, Set.EqOn u v S → f u = f v)
    (hg : ∀ u v, Set.EqOn u v T → g u = g v) (a : A) (b : B) :
    (∃ w, f w = a ∧ g w = b) ↔
      ∃ u v, f u = a ∧ g v = b ∧ Set.EqOn u v (S ∩ T) := by
  classical
  constructor
  · rintro ⟨w, h₁, h₂⟩
    exact ⟨w, w, h₁, h₂, fun _ _ ↦ rfl⟩
  · rintro ⟨u, v, hu, hv, huv⟩
    let w (i : I) := if i ∈ S then u i else v i
    refine ⟨w, (hf w u ?_).trans hu, (hg w v ?_).trans hv⟩
    · intro i hi
      simp [w, hi]
    · intro i hi
      by_cases hs : i ∈ S
      · simpa [w, hs] using huv (show i ∈ S ∩ T from ⟨hs, hi⟩)
      · simp [w, hs]
