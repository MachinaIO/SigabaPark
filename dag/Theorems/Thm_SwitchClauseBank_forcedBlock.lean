import Definitions.Def_SwitchClauseBank
import Mathlib.Tactic

theorem SwitchClauseBank.forcedBlock {I : Type*} (F : Set (Set I)) (i j : I) :
    (j ∈ SwitchClauseBank.forced F i ∧
      ¬ ∃ k ∈ SwitchClauseBank.forced F i,
        SwitchClauseBank.forced F k ≠ SwitchClauseBank.forced F i ∧
        j ∈ SwitchClauseBank.forced F k) ↔
      SwitchClauseBank.forced F j = SwitchClauseBank.forced F i := by
  sorry
