import Mathlib.Tactic

theorem SwitchClauseBank.unionGuard {X I J : Type*} (h : X → Prop) (a : I → X → Prop) (b : J → X → Prop) :
    (∀ x, h x → (∀ i, a i x) ∨ (∀ j, b j x)) ↔
      ∀ i j x, h x → ¬ (¬ a i x ∧ ¬ b j x) := by
  sorry
