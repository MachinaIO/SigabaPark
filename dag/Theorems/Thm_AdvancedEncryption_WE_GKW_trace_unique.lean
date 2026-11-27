import Definitions.Def_WE_GKW_Trace

open SigabaNeo AdvancedEncryption.WE.GKW

theorem AdvancedEncryption.WE.GKW.trace_unique (w : List Bool) (gs : GateList) (b : Bool) :
    ∃ t, TraceFits w gs t ∧ gs.foldl estep (w, b) = (w ++ t, t.getLastD b) ∧
      ∀ u, TraceFits w gs u → u = t := by sorry
