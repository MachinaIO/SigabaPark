import Definitions.Def_WE_TraceLampSamples

theorem solution (w : List Bool) (gs : SigabaNeo.GateList) (zs : List Bool) :
    (gs.length = zs.length ∧
       ((AdvancedEncryption.WE.TraceLamp.samples w gs zs).filter
         (fun g ↦ g.2.2 != !(g.1 && g.2.1))) = []) ↔
      AdvancedEncryption.WE.GKW.TraceFits w gs zs := by
  induction gs generalizing w zs with
  | nil => cases zs <;> simp [AdvancedEncryption.WE.TraceLamp.samples, AdvancedEncryption.WE.GKW.TraceFits]
  | cons g gs ih =>
    cases zs with
    | nil => simp [AdvancedEncryption.WE.TraceLamp.samples, AdvancedEncryption.WE.GKW.TraceFits]
    | cons z zs =>
      by_cases h : z = !(w.getD g.1 true && w.getD g.2 true)
      · simp [AdvancedEncryption.WE.TraceLamp.samples, AdvancedEncryption.WE.GKW.TraceFits, h, ← ih]
      · simp at h
        simp [AdvancedEncryption.WE.TraceLamp.samples, AdvancedEncryption.WE.GKW.TraceFits, h]
