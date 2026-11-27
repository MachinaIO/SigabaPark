import Mathlib

theorem AdvancedEncryption.WE.TraceProject.cube_descent {V : Type} [DecidableEq V] (S : Finset V) (H : Finset V → Prop) [DecidablePred H]
    (top : H S) (par : Even ((S.powerset.filter H).card)) :
    ∃ T, T ⊂ S ∧ H T := by
  sorry
