import Definitions.Def_WE_UnaryTraceWalk

open SigabaNeo Turing AdvancedEncryption.WE AdvancedEncryption.WE.UnaryTraceWalk

theorem AdvancedEncryption.WE.UnaryTraceWalk.run_spec (x : Fin 128 → Bool) (t : Fin 4096 → Bool)
    (φ : CircuitSAT.Circuit 128 4096) :
    machine.run (word x t φ) = PMF.pure
      [decide (List.ofFn t = trace (List.ofFn x) φ.gates) && evalGates (List.ofFn x, φ.gates)] := by sorry
