import Mathlib

theorem solution (m base r out : Bool) :
    (m ^^ base) ^^ (base ^^ r) ^^ (out && r) = m ^^ ((!out) && r) := by
  revert m base r out
  decide
