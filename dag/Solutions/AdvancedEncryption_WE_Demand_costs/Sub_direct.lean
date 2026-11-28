import Definitions.Def_NandDemandRoles

open DemandPolicy DemandRole SigabaNeo

theorem solution :
    enc.states=4818 ∧ enc.tapes=4 ∧ enc.time=1000000000 ∧ enc.descLen=77271084 ∧
    dec.time=210000000 ∧ dec.descLen=294 ∧ enc.cost+dec.cost=1287271378 ∧
    enc.cost+dec.cost<2^32 := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,by decide⟩
