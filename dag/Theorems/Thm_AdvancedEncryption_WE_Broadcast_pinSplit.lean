import Definitions.Def_SemSep

open SemSep

theorem AdvancedEncryption.WE.Broadcast.pinSplit (h r : Nat) (tail : List Bool) (x : Bool) :
    applyRows (((List.replicate h true) ++ false::tail).take r) x =
      if r≤h then flipN r x else applyRows (tail.take (r-(h+1))) true := by sorry
