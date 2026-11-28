import Definitions.Def_SemSepRole

open SemSepRole

theorem solution :
    enc.time=35000000 ∧ dec.time=70000000 ∧ enc.descLen=1181883420 ∧
    dec.descLen=294 ∧ enc.cost+dec.cost=1286883714 ∧ enc.cost+dec.cost<2^32 := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,by decide⟩
