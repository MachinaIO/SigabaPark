import Definitions.Def_SerpentineBankMachine
open SerpentineLaws SerpentineRing SigabaNeo.Lattices.Algo Cslib
theorem AdvancedEncryption.WE.Serpentine.negation : ∀ x : Fin 16, neg4 x.val = (16-x.val)%16 := by sorry
