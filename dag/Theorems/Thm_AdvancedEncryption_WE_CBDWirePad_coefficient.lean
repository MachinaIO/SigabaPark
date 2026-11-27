import SigabaNeoStd.Lattices.RingLWE
open SigabaNeo.Lattices Cslib.Probability

theorem AdvancedEncryption.WE.CBDWirePad.coefficient : ModuleLWE.coeffLaw 256 (.cbd 1) =
    (Cslib.Probability.PMF.uniformOfFintype (Bool × Bool)).map
      (fun ab => ((if ab.1 then (1:ZMod 256) else 0) -
                  (if ab.2 then (1:ZMod 256) else 0))) := by sorry
