import Definitions.Def_QuadraticNandCut
open AffineNandCut
open scoped BigOperators
theorem AdvancedEncryption.WE.QuadraticCut.pivot (r l m : Bool) :
    (∑ x : Bool, ∑ y : Bool, sgn (r ^^ (x && l) ^^ (y && m) ^^ (x && y)))
      =2*sgn (r ^^ (l && m)) := by sorry
