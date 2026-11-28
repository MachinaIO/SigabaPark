import Definitions.Def_NandDemandRoles

open DemandPolicy DemandRole SigabaNeo

theorem solution (gs : GateList) (need ds : List (Option Bool)) (xs : List Bool)
    (prev : Option Bool) (v : Bool) (h : cert need prev gs ds) (hh : List.Forall₂ fits need xs)
    (hv : fits prev v) : (gs.foldl estep (xs,v)).2=true := by
  induction gs generalizing need ds xs prev v with
  | nil =>
    cases ds with
    | cons => exact False.elim h
    | nil => change prev=some true at h;subst prev;simpa [fits,eq_comm] using hv
  | cons g gs ih =>
    obtain ⟨a,b⟩:=g
    cases ds with
    | nil => exact False.elim h
    | cons d ds =>
      obtain ⟨lo,hi,nxt⟩:=h
      have hp:=child_ok d _ _ _ _ (atWire _ _ hh a) (atWire _ _ hh b) lo hi
      exact ih (need++[d]) ds _ d _ nxt (snoc hh hp) hp
