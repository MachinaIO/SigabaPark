import Definitions.Def_NandWalshBox
open NandWalshBox
theorem solution (a b c : Bool) (t : Bool × Bool × Bool × Bool × Bool) :
    liftOK a b c t ↔ c = !(a && b) ∧ t = ((!a && !b),(!a && b),(a && !b),(a && b),a) := by
  revert a b c t
  decide
