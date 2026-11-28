import Definitions.Def_SerpentineBankMachine
open SerpentineLaws SerpentineRing SigabaNeo.Lattices.Algo Cslib
theorem AdvancedEncryption.WE.Serpentine.fusedNibble : ∀ (d : Fin 2) (a k : Fin 16),
    runWord d.val a.val k.val 0 = dot 4 d.val ((a.val*k.val)%16) 0 0 0 := by sorry
