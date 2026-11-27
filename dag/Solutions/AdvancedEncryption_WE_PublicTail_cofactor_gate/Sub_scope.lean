import Mathlib

theorem solution {P U : Type} (phi : P → U → Prop) (payload : Prop) (p : P) (u : U) :
    (phi p u ∧ (payload ∧ ∃ v, phi p v)) ↔ (payload ∧ phi p u) := by
  constructor
  · rintro ⟨hx, hb, _⟩
    exact ⟨hb, hx⟩
  · rintro ⟨hb, hx⟩
    exact ⟨hx, hb, u, hx⟩
