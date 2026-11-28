import Definitions.Def_SignedColorEnergy

open SignedColorEnergy

theorem AdvancedEncryption.WE.SignedColor.GateTrace (x : List Bool) (gs : SigabaNeo.GateList) :
    accepted (true :: x, true) gs ↔ SigabaNeo.evalGates (x,gs) = true := by sorry
