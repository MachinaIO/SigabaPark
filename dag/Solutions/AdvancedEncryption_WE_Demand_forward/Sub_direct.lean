import Definitions.Def_NandDemandRoles

open DemandPolicy DemandRole SigabaNeo

theorem solution (gs : GateList) (ps : List (Option Bool)) (xs : List Bool) (last : Bool)
    (h : List.Forall₂ fits ps xs) :
    List.Forall₂ fits (gs.foldl astep ps) (gs.foldl estep (xs,last)).1 := by
  induction gs generalizing ps xs last with
  | nil => exact h
  | cons g gs ih =>
    simp only [List.foldl_cons]
    apply ih
    exact snoc h (localUpper _ _ _ _ (atWire _ _ h g.1) (atWire _ _ h g.2))
