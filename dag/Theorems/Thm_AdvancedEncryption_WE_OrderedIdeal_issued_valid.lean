import Definitions.Def_OrderedNand

open OrderedNand SigabaNeo

theorem AdvancedEncryption.WE.OrderedIdeal.issued_valid (gs : GateList) (x : List Bool) (last : Bool) (p q y : Key)
    (mem : issued (true::x).length gs p q y) :
    let v := val (gs.foldl estep (true::x,last)).1
    live v p → live v q → live v y := by sorry
