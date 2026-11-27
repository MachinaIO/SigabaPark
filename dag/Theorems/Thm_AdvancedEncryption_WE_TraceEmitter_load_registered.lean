import Definitions.Def_WE_TraceEmitterStep
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List

open Turing SigabaNeo AdvancedEncryption.WE.TraceEmitter

theorem AdvancedEncryption.WE.TraceEmitter.load_registered (params stmt wit tail : List Bool) :
    let x := MultiTapeTM.frame params ++ MultiTapeTM.frame stmt ++ MultiTapeTM.frame wit ++ tail
    let off := 2*params.length + 2*stmt.length + 2*wit.length + 3
    tm.runFrom (tm.initCfg x) (2*params.length + 3*stmt.length + 3*wit.length + 7) =
      snap x off stmt (true :: wit) 0 0 (some .first) := by
  sorry
