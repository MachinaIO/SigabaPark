import Definitions.Def_OrderedNand

open OrderedNand SigabaNeo

theorem AdvancedEncryption.WE.OrderedIdeal.full_fold (gs : GateList) (x : List Bool) (b : Bool) :
    (compiled (true::x).length gs).foldl estep (true::x,b) = gs.foldl estep (true::x,b) := by sorry
