import Definitions.Def_BinaryBilinearCounts
open BinaryBilinearCounts

theorem AdvancedEncryption.WE.BinaryBilinear.character_cell (a b c : Bool) : scalarSum a b c =
    if c then 2 * sign (a && b) else if a || b then 0 else 4 := by
  sorry
