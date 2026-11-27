import Definitions.Def_DensityTrials

open AdvancedEncryption.WE.DensityTrials

theorem AdvancedEncryption.WE.DensityTrials.batch_lane {I : Type} (inputs : List (I → Bool)) (gs : SigabaNeo.GateList) (i : I) :
    (gs.foldl batchStep ((fun _ => true) :: inputs, fun _ => true)).2 i =
      SigabaNeo.evalGates (inputs.map (fun c => c i), gs) := by sorry
