import Definitions.Def_SerpentineBankMachine
open SerpentineLaws SerpentineRing SigabaNeo.Lattices.Algo Cslib
theorem solution : ∀ x : Fin 16, neg4 x.val = (16-x.val)%16 := by decide
