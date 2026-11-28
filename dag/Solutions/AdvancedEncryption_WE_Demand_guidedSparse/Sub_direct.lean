import Definitions.Def_NandDemandRoles

open DemandPolicy DemandRole SigabaNeo

theorem solution (p m : Map) (v : Nat→Bool) (gs : List G) (hp : valid p v) (hm : valid m v)
    (hg : ∀ g∈gs,v g.1= !(v g.2.1 && v g.2.2)) :
    ∃ cs m', cs.length≤gs.length ∧ sparse p gs cs m=some m' ∧ valid m' v := by
  obtain ⟨cs,f,_,h,ok⟩ := guided p m v gs hp hm hg
  obtain ⟨bs,len,hb⟩ := compact p m f gs cs h
  exact ⟨bs,f,len,hb,ok⟩
