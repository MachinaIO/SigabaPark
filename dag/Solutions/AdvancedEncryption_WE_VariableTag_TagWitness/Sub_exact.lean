import Definitions.Def_VariableTagFront

theorem solution (f : Fin 16 → Fin 256 → Fin 16) (v : Fin 16) :
    (∀ i, ∃ u, f i u = v) ↔ ∃ w : Fin 16 → Fin 256, ∀ i, f i (w i) = v := by
  constructor
  · intro h
    exact ⟨fun i => (h i).choose, fun i => (h i).choose_spec⟩
  · rintro ⟨w, hw⟩ i
    exact ⟨w i, hw i⟩
