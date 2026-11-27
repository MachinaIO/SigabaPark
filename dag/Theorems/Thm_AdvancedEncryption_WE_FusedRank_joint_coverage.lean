import Mathlib.Logic.Function.Basic

theorem AdvancedEncryption.WE.FusedRank.joint_coverage {W Z : Type} (address : W → Z) :
    Function.Surjective address ↔
      ∀ test : Z → Prop, (∀ w, ¬test (address w)) → ∀ z, ¬test z := by
  sorry
