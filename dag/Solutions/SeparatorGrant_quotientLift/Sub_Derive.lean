import Mathlib.Tactic

theorem solution {S Q : Type*} (q : S → Q) (extend : S → Prop)
    (lift : ∀ x y, q x = q y → extend x → extend y) (s : S) :
    (∃ t, q t = q s ∧ extend t) ↔ extend s := by
  constructor
  · rintro ⟨t, ht, he⟩
    exact lift t s ht he
  · intro h
    exact ⟨s, rfl, h⟩
