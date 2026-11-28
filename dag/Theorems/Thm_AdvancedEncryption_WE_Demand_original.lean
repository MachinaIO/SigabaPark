import Definitions.Def_NandDemandRoles

open DemandPolicy DemandRole SigabaNeo

theorem AdvancedEncryption.WE.Demand.original (gs : GateList) (need ds : List (Option Bool)) (xs : List Bool)
    (prev : Option Bool) (v : Bool) (h : cert need prev gs ds) (hh : List.Forall₂ fits need xs)
    (hv : fits prev v) : (gs.foldl estep (xs,v)).2=true := by sorry
