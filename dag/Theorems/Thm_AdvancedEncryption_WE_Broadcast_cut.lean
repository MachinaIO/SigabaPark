import Definitions.Def_SemSep

open SemSep

theorem AdvancedEncryption.WE.Broadcast.cut {S X : Type} (T : S→X→S) (ok : S→Bool) (s : S) (a b : List X) :
    accept T ok s (a++b)=true ↔ ∃! q, a.foldl T s=q ∧ accept T ok q b=true := by sorry
