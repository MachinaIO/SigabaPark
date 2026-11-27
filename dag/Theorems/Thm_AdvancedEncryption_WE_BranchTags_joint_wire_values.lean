import Mathlib.Data.Set.Operations

theorem AdvancedEncryption.WE.BranchTags.joint_wire_values
    {I V A B : Type*} (S T : Set I) (f : (I → V) → A) (g : (I → V) → B)
    (hf : ∀ u v, Set.EqOn u v S → f u = f v)
    (hg : ∀ u v, Set.EqOn u v T → g u = g v) (a : A) (b : B) :
    (∃ w, f w = a ∧ g w = b) ↔
      ∃ u v, f u = a ∧ g v = b ∧ Set.EqOn u v (S ∩ T) := by sorry
