import Definitions.Def_NandDemandRoles

open DemandPolicy DemandRole SigabaNeo

theorem AdvancedEncryption.WE.Demand.forward (gs : GateList) (ps : List (Option Bool)) (xs : List Bool) (last : Bool)
    (h : List.Forall₂ fits ps xs) :
    List.Forall₂ fits (gs.foldl astep ps) (gs.foldl estep (xs,last)).1 := by sorry
