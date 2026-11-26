import Definitions.Def_WE_SuccinctInstanceDecoder

open Turing.MultiTapeTM SigabaNeo SigabaNeo.Lattices
open AdvancedEncryption.WE.Assumptions.SuccinctLWE AdvancedEncryption.WE.SuccinctInstanceDecoder

open Cslib.Probability

theorem AdvancedEncryption.WE.SuccinctInstanceDecoder.read_encode_lawWith (p : Params) :
    (∀ x : Instance p, read p (encode p x) = x) ∧
    (∀ {V : Type} (second : Matrix (Fin p.n) (Fin p.m) (ZMod p.q) → PMF (Fin p.m → ZMod p.q))
      (K : Instance p → PMF V),
      (lawWith p second).bind (fun w ↦ K (read p w)) =
        (do
          let B ← PMF.uniformOfFintype (Matrix (Fin p.n) (Fin p.m) (ZMod p.q))
          let b ← second B
          let W ← PMF.uniformOfFintype (Matrix (Fin (p.ℓ * p.n)) (Fin p.m) (ZMod p.q))
          let T ← trapdoorLaw p B W
          K (B, b, W, T))) := by
  sorry
