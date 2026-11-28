import Mathlib

theorem solution (test : Fin 3 → Bool → Bool → Prop)
    (h0 : ∀ u v, test 0 u v ↔ u = false)
    (h1 : ∀ u v, test 1 u v ↔ v = true)
    (h2 : ∀ u v, test 2 u v ↔ u = v) :
    (∀ i, ∃ u v, test i u v) ∧ ¬ ∃ u v, ∀ i, test i u v := by
  constructor
  · intro i
    fin_cases i
    · exact ⟨false, false, (h0 _ _).2 rfl⟩
    · exact ⟨true, true, (h1 _ _).2 rfl⟩
    · exact ⟨false, false, (h2 _ _).2 rfl⟩
  · rintro ⟨u, v, h⟩
    have hu := (h0 _ _).1 (h 0)
    have hv := (h1 _ _).1 (h 1)
    have huv := (h2 _ _).1 (h 2)
    simp_all
