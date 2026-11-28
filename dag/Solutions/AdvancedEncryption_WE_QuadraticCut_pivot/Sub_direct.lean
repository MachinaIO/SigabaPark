import Definitions.Def_QuadraticNandCut
open AffineNandCut
open scoped BigOperators
theorem solution (r l m : Bool) :
    (∑ x : Bool, ∑ y : Bool, sgn (r ^^ (x && l) ^^ (y && m) ^^ (x && y)))
      =2*sgn (r ^^ (l && m)) := by
  cases r <;> cases l <;> cases m <;> decide
