import Mathlib.Tactic

theorem SeparatorGrant.quotientLift {S Q : Type*} (q : S → Q) (extend : S → Prop)
    (lift : ∀ x y, q x = q y → extend x → extend y) (s : S) :
    (∃ t, q t = q s ∧ extend t) ↔ extend s := by
  sorry
