import Mathlib.Tactic

namespace QuarterPhaseFiber

/-- Real sign of a binary phase. -/
def sign (x : Bool) : Int := if x then -1 else 1

/-- The signed contribution of one bent pair and one linear frequency. -/
def pair (a b x y : Bool) : Int :=
  sign ((x && y) ^^ (a && x) ^^ (b && y))

end QuarterPhaseFiber
