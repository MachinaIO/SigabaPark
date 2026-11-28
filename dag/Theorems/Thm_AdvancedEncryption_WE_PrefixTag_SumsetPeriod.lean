import Mathlib

theorem AdvancedEncryption.WE.PrefixTag.SumsetPeriod {G : Type*} [AddCommGroup G] (S T : G → Prop) (h : G)
    (period : ∀ x, S (x+h) ↔ S x) (z : G) :
    (∃ a b, S a ∧ T b ∧ a+b = z+h) ↔ (∃ a b, S a ∧ T b ∧ a+b = z) := by sorry
