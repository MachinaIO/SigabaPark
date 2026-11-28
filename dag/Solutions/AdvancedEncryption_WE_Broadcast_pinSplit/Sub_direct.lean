import Definitions.Def_SemSep

open SemSep

theorem solution (h r : Nat) (tail : List Bool) (x : Bool) :
    applyRows (((List.replicate h true) ++ false::tail).take r) x =
      if r≤h then flipN r x else applyRows (tail.take (r-(h+1))) true := by
  induction h generalizing r x with
  | zero => cases r <;> simp [applyRows,flipN,nand]
  | succ h ih =>
    cases r with
    | zero => simp [applyRows,flipN]
    | succ r => simpa [List.replicate_succ,applyRows,nand,flipN,Nat.succ_le_succ_iff] using ih r (!x)
