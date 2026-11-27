import Definitions.Def_SparseAtomPair

open SparseAtomPair

theorem solution :
    enc.time = 671651 ∧ dec.time = 24704 ∧ enc.descLen = 1291468860 ∧
    dec.descLen = 26083068 ∧ enc.cost + dec.cost = 1318248283 ∧
    enc.cost + dec.cost < 2^32 := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,by decide⟩
