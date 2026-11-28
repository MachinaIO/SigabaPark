import Mathlib.Tactic

namespace SwitchClauseBank

/-- Coordinates occurring in every support that contains i. -/
def forced {I : Type*} (F : Set (Set I)) (i : I) : Set I :=
  {j | ∀ t ∈ F, i ∈ t → j ∈ t}

/-- Coordinatewise Boolean majority. -/
def maj (a b c : Bool) : Bool := (a && b) || (a && c) || (b && c)

end SwitchClauseBank
