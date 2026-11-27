import Definitions.Def_WE_TraceEmitter
import Definitions.Def_WE_CircuitSAT

open Turing SigabaNeo AdvancedEncryption.WE AdvancedEncryption.WE.TraceEmitter

theorem AdvancedEncryption.WE.TraceEmitter.run_registered (φ : CircuitSAT.Circuit 128 4096) (w : Fin 128 → Bool) (ct : List Bool) :
    let rel := CircuitSAT.relation 128 4096
    let word := encodeTuple [paramsWord rel CircuitSAT.params, rel.encStmt φ, rel.encWit w, ct]
    let hist := true :: List.ofFn w
    let trace := (φ.gates.foldl estep (hist,true)).1.drop hist.length
    machine.run word = PMF.pure (MultiTapeTM.frame trace) := by
  sorry
