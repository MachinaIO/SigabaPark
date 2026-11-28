import Mathlib

theorem AdvancedEncryption.WE.BinaryBilinear.triple_discrepancy (a b c x y z : Bool) :
    (((a && x) ^^ (b && y)) ^^ (c && z)) ^^ (((a ^^ b) ^^ c) && ((x ^^ y) ^^ z)) =
      ((a ^^ b) && (x ^^ z)) ^^ ((a ^^ c) && (x ^^ y)) := by
  sorry
