import Definitions.Def_LinearProjectNative
theorem solution :
    LinearProjectRole.enc.states=236109 ∧ LinearProjectRole.enc.time=112537198 ∧
    LinearProjectRole.enc.descLen=110499012 ∧ LinearProjectRole.dec.cost=11172189 ∧
    LinearProjectRole.enc.cost+LinearProjectRole.dec.cost=234208399 ∧
    LinearProjectRole.enc.cost+LinearProjectRole.dec.cost<2^32 := by decide
