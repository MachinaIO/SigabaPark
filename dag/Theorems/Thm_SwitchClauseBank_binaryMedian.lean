import Definitions.Def_SwitchClauseBank
import Mathlib.Tactic

theorem SwitchClauseBank.binaryMedian : ∀ a b c d e f : Bool,
    (a || d) = true → (b || e) = true → (c || f) = true →
    (SwitchClauseBank.maj a b c || SwitchClauseBank.maj d e f) = true := by
  sorry
