import Definitions.Def_SerpentineBankMachine
open SerpentineLaws SerpentineRing SigabaNeo.Lattices.Algo Cslib
theorem AdvancedEncryption.WE.Serpentine.budgetCosts :
    (machine 1024 337 true).cost=1469656881 ∧
    (machine 1024 548 true).cost=2364378749 ∧
    (machine 1024 86 false).cost=405319493 ∧
    (SerpentineBank.machine 1024 548 171 8192).states=72960 ∧
    (SerpentineBank.machine 1024 548 171 8192).descLen=390044160 ∧
    (SerpentineBank.machine 1024 548 171 8192).time=3104682541 ∧
    (SerpentineBank.machine 1024 337 171 8192).cost=2300681921 ∧
    (SerpentineBank.machine 1024 548 171 8192).cost+
      (machine 1024 86 false).cost+394921102=2^32 := by sorry
