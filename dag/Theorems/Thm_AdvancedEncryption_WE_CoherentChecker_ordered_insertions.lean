import Definitions.Def_CoherentCheckerExpansion
open CoherentCheckerExpansion

theorem AdvancedEncryption.WE.CoherentChecker.ordered_insertions {R : Type} [Ring R] (l : List (R × R)) :
    actual l - zeros l = (singles l).sum + (pairs l).sum ∧
    (singles l).length = l.length ∧ (pairs l).length = l.length.choose 2 := by
  sorry
