import Definitions.Def_WE_TraceLampSamples

theorem AdvancedEncryption.WE.TraceLamp.samples_fit (w : List Bool) (gs : SigabaNeo.GateList) (zs : List Bool) :
    (gs.length = zs.length ∧
       ((AdvancedEncryption.WE.TraceLamp.samples w gs zs).filter
         (fun g ↦ g.2.2 != !(g.1 && g.2.1))) = []) ↔
      AdvancedEncryption.WE.GKW.TraceFits w gs zs := by
  sorry
