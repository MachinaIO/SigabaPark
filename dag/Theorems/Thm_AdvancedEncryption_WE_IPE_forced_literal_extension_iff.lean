import Lean

theorem AdvancedEncryption.WE.IPE.forced_literal_extension_iff {α : Type} (neg : α → α) (inv : ∀ a, neg (neg a) = a)
    (R : α → α → Prop) (refl : ∀ a, R a a)
    (trans : ∀ {a b c}, R a b → R b c → R a c)
    (contra : ∀ {a b}, R a b → R (neg b) (neg a))
    (base : ∀ a, ¬ (R a (neg a) ∧ R (neg a) a))
    (required : α → Prop) (vars : List α) :
    (∀ a b, required a → required b → ¬ R a (neg b)) ↔
    ∃ S : α → Prop, (∀ a, required a → S a) ∧
      (∀ a b, S a → R a b → S b) ∧ (∀ a, S a → ¬ S (neg a)) ∧
      (∀ a ∈ vars, S a ∨ S (neg a)) := by
  sorry
