import Mathlib

theorem solution {C Y I : Type*} (test : I → C → Y → Prop) (i : Finset I) (core : C) (opening : Y)
    (accepted : ∀ a ∈ i, test a core opening) : ∃ extension, ∀ a ∈ i, test a core extension := by
  exact ⟨opening, accepted⟩
