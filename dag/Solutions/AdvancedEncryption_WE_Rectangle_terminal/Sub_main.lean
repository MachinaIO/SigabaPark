import Definitions.Def_TerminalRectangle

open TerminalRectangle

theorem solution (h : HiddenRole) (t j : Bool) (a c : Bool → Bool) (u v : Bool) :
    (body t j (a true) (c true) =
      (body t j (a false) (c false) ^^ body t j (a false) (c true) ^^ body t j (a true) (c false))) ∧
    body (!t) (flipJoin h j)
      (flipLeft h (a u))
      (flipRight h (c v)) = body t j (a u) (c v) := by
  constructor
  · generalize a true = at_; generalize a false = af
    generalize c true = ct; generalize c false = cf
    cases t <;> cases j <;> cases at_ <;> cases af <;> cases ct <;> cases cf <;> rfl
  · cases h <;> cases t <;> cases j <;> cases ha : a u <;> cases hc : c v <;> rfl
