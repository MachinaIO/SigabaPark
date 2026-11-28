import Definitions.Def_QuadraticNandCut
open AffineNandCut
open scoped BigOperators
theorem solution (l r : Bool) (h : (l || r)=true) :
    ∀ t : Bool, ∃ x y : Bool, ((x && y) ^^ ((l || x) && (r || y)))=t := by
  intro t; cases l <;> cases r <;> cases t <;> first | contradiction | decide
