import Definitions.Def_SuccinctLWE
import CslibFrontier.Probability.StatisticalDistance.CloseTo

open AdvancedEncryption.WE.Assumptions.SuccinctLWE Cslib.Probability
open scoped ENNReal

theorem AdvancedEncryption.WE.LeafView.encodedLaw_close_of_setup (p : Params)
    (setup : PMF (Matrix (Fin p.n) (Fin p.m) (ZMod p.q) ×
      Matrix (Fin (p.ℓ * p.n)) (Fin p.m) (ZMod p.q) ×
      Option (Matrix (Fin (p.ℓ * p.m + p.m)) (Fin (p.ℓ * (p.n * p.k))) ℤ)))
    (second : Matrix (Fin p.n) (Fin p.m) (ZMod p.q) → PMF (Fin p.m → ZMod p.q))
    (ε : ℝ≥0∞)
    (h : CloseTo setup
      ((PMF.uniformOfFintype (Matrix (Fin p.n) (Fin p.m) (ZMod p.q))).bind fun B ↦
        (PMF.uniformOfFintype (Matrix (Fin (p.ℓ * p.n)) (Fin p.m) (ZMod p.q))).bind fun W ↦
          (trapdoorLaw p B W).map fun T ↦ (B, W, T)) ε) :
    CloseTo (setup.bind fun x ↦
      (second x.1).map fun b ↦ encode p (x.1, b, x.2.1, x.2.2)) (lawWith p second) ε := by
  sorry
