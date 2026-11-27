import Definitions.Def_WE_UnaryTraceWalk

open SigabaNeo Turing AdvancedEncryption.WE AdvancedEncryption.WE.UnaryTraceWalk

theorem AdvancedEncryption.WE.UnaryTraceWalk.machine_budget :
    machine.Deterministic ∧ machine.time = 173064452 ∧ machine.descLen = 5728050 ∧
      machine.cost < 2 ^ 32 := by sorry
