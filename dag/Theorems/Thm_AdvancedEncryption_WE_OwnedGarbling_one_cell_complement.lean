import Definitions.Def_OwnedGarbling

open OwnedGarbling
open scoped BigOperators

theorem AdvancedEncryption.WE.OwnedGarbling.one_cell_complement {K : Type} [Fintype K] (test : Bool × K → ℝ) :
    (∑ v : Bool × K × K, test (!v.1, v.2.2)) =
      ∑ v : Bool × K × K, test (v.1, v.2.1) := by sorry
