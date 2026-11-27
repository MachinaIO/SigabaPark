import Definitions.Def_TableauShiftAudit

open ShiftPairView

theorem AdvancedEncryption.WE.TableauAudit.pair_laws (r f₀ f₁ : Bool) : tag (tag r f₀ f₁) f₀ f₁ = r ∧
    acceptingCount r false = 1 ∧ acceptingCount r true = 3 := by
  sorry
