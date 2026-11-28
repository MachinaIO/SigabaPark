import Definitions.Def_QuadraticNandCut
open AffineNandCut
open scoped BigOperators
theorem solution (x u y v : Bool) :
    ((x && y) ^^ (u && v)) = (((x ^^ u) && y) ^^ (u && (y ^^ v))) := by
  cases x <;> cases u <;> cases y <;> cases v <;> decide
