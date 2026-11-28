import Definitions.Def_SerpentineBankMachine
open SerpentineLaws SerpentineRing SigabaNeo.Lattices.Algo Cslib
theorem AdvancedEncryption.WE.Serpentine.threshold :
    (SerpentineBank.machine 1024 617 171 8192).cost + (machine 1024 86 false).cost < 2^32 ∧
    2^32 < (SerpentineBank.machine 1024 618 171 8192).cost + (machine 1024 86 false).cost ∧
    (SerpentineBank.machine 1024 689 171 8192).cost < 2^32 ∧
    2^32 < (SerpentineBank.machine 1024 690 171 8192).cost := by sorry
