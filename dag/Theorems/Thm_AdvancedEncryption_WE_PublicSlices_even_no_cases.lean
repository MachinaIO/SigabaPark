import Mathlib

theorem AdvancedEncryption.WE.PublicSlices.even_no_cases {X Y J : Type} (u : X → Set J) (v : Y → Set J)
    (h : ∀ x y, u x ∩ v y = ∅ ∨ u x ∩ v y = Set.univ) :
    (∀ x y, u x ∩ v y = ∅) ∨
      ((∀ x, u x = ∅ ∨ u x = Set.univ) ∧ (∀ y, v y = ∅ ∨ v y = Set.univ)) := by
  sorry
