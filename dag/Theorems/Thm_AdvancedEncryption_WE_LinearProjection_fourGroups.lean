import Definitions.Def_LinearObservationJoin
open ObservationJoin
theorem AdvancedEncryption.WE.LinearProjection.fourGroups (u v x y : Bool) :
    (∃ a b c d : Bool, ((a ^^ c)=u ∧ (b ^^ d)=v ∧ (a ^^ b)=x ∧ (c ^^ d)=y)) ↔
      (u ^^ v)=(x ^^ y) := by sorry
