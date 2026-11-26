import Definitions.Def_SuccinctLWE

open AdvancedEncryption.WE.Assumptions.SuccinctLWE Cslib.Probability

theorem AdvancedEncryption.WE.LeafView.succinctIdeal_augmented (p : Params) :
    idealLaw p =
      (PMF.uniformOfFintype (Matrix (Option (Fin p.n)) (Fin p.m) (ZMod p.q))).bind fun A ↦ do
        let B := fun i ↦ A (some i)
        let W ← PMF.uniformOfFintype (Matrix (Fin (p.ℓ * p.n)) (Fin p.m) (ZMod p.q))
        let T ← trapdoorLaw p B W
        return encode p (B, A none, W, T) := by
  sorry
