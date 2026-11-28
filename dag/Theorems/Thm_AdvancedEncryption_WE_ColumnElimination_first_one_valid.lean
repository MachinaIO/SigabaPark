import Definitions.Def_ColumnElimination

open AdvancedEncryption.WE.ColumnElimination

theorem AdvancedEncryption.WE.ColumnElimination.first_one_valid {m : Nat} (a : Fin m → ZMod 2) :
    a = 0 ∨ firstOne a a = 1 := by sorry
