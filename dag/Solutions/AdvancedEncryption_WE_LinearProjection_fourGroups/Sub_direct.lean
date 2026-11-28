import Definitions.Def_LinearObservationJoin
open ObservationJoin
theorem solution (u v x y : Bool) :
    (∃ a b c d : Bool, ((a ^^ c)=u ∧ (b ^^ d)=v ∧ (a ^^ b)=x ∧ (c ^^ d)=y)) ↔
      (u ^^ v)=(x ^^ y) := by
  cases u <;> cases v <;> cases x <;> cases y <;> decide
