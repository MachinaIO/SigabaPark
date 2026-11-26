import Mathlib.Tactic.Common

theorem solution {n U : ℕ} {α β : Type*} (L : Fin n → Fin U → Bool → α)
    (E : (Fin n → Bool) → β) (g : Fin n → Fin U → β → α)
    (hrel : ∀ w i u, g i u (E w) = L i u (w i)) :
    ∀ i u b, ∃ w ∈ ({fun _ => false, fun _ => true} : Set (Fin n → Bool)),
      g i u (E w) = L i u b := by
  intro i u b
  refine ⟨fun _ => b, ?_, hrel _ i u⟩
  cases b
  · exact Or.inl rfl
  · exact Or.inr rfl
