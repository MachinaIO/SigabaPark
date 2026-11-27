import Definitions.Def_AffineFiberScan

open AdvancedEncryption.WE.AffineFiberScan

theorem AdvancedEncryption.WE.AffineFiberScan.scan_sound {W D : Type} (d : Domain W D) (w : W) (gates : SigabaNeo.GateList)
    (input : List Bool) (labels : List D)
    (h : List.Forall₂ (fun a x => d.holds a x w) labels input) :
    d.holds (gates.foldl (advance d) (d.one :: labels, d.one)).2
      (SigabaNeo.evalGates (input, gates)) w := by sorry
