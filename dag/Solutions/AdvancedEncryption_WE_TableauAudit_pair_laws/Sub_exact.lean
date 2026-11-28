import Definitions.Def_TableauShiftAudit

open ShiftPairView

theorem solution (r f₀ f₁ : Bool) : tag (tag r f₀ f₁) f₀ f₁ = r ∧
    acceptingCount r false = 1 ∧ acceptingCount r true = 3 := by
  exact ⟨singleTagPermutation f₀ f₁ r, by cases r <;> decide⟩
