import Mathlib.Tactic

theorem solution {X I J : Type*} (h : X → Prop) (a : I → X → Prop) (b : J → X → Prop) :
    (∀ x, h x → (∀ i, a i x) ∨ (∀ j, b j x)) ↔
      ∀ i j x, h x → ¬ (¬ a i x ∧ ¬ b j x) := by
  classical
  constructor
  · intro ht i j x hx hn
    rcases ht x hx with ha | hb
    · exact hn.1 (ha i)
    · exact hn.2 (hb j)
  · intro ht x hx
    by_cases ha : ∀ i, a i x
    · exact Or.inl ha
    · push_neg at ha
      obtain ⟨i,hi⟩ := ha
      exact Or.inr (fun j ↦ by
        by_contra hj
        exact ht i j x hx ⟨hi,hj⟩)
