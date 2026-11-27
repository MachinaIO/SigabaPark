import Definitions.Def_SemSep

open SemSep

theorem AdvancedEncryption.WE.Broadcast.general {A : Type} (op : A→A→A) (xs ys : List A) (old new : A→A) :
    Expanded op (shape old new xs) ys ↔ ys=scan op old new xs := by sorry
