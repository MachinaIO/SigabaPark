import Definitions.Def_OwnedGarbling

open OwnedGarbling
open scoped BigOperators

theorem solution {P C I : Type} [Fintype P] [Fintype C] [Fintype I]
    [DecidableEq P] [DecidableEq C] [DecidableEq I] (who : C → I → P)
    (theta : P → ZMod 2) (a : C → I → ZMod 2) (test : Tape P C I → ℝ) :
    (∑ coins : Tape P C I, test (affineCoins who theta a coins)) = ∑ visible, test visible := by
  exact (affineCoins who theta a).sum_comp test
