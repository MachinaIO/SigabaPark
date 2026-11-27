import Mathlib.Tactic.Ring

theorem AdvancedEncryption.WE.BranchTags.quadratic_tag_pair_unique
    {F : Type*} [CommRing F] [IsDomain F] (h₂ : (2 : F) ≠ 0) (a b c d : F) :
    (a + b = c + d ∧ a ^ 2 + b ^ 2 = c ^ 2 + d ^ 2) ↔
      (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by sorry
