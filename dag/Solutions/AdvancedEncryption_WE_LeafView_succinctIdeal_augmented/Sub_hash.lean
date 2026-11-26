import Definitions.Def_SuccinctLWE

open AdvancedEncryption.WE.Assumptions.SuccinctLWE Cslib.Probability

theorem solution (p : Params) :
    idealLaw p =
      (PMF.uniformOfFintype (Matrix (Option (Fin p.n)) (Fin p.m) (ZMod p.q))).bind fun A ↦ do
        let B := fun i ↦ A (some i)
        let W ← PMF.uniformOfFintype (Matrix (Fin (p.ℓ * p.n)) (Fin p.m) (ZMod p.q))
        let T ← trapdoorLaw p B W
        return encode p (B, A none, W, T) := by
  let e : (Matrix (Fin p.n) (Fin p.m) (ZMod p.q) × (Fin p.m → ZMod p.q)) ≃
      Matrix (Option (Fin p.n)) (Fin p.m) (ZMod p.q) :=
    { toFun := fun v i ↦ i.elim v.2 v.1
      invFun := fun A ↦ ((fun i ↦ A (some i)), A none)
      left_inv := fun _ ↦ rfl
      right_inv := fun A ↦ funext fun i ↦ by cases i <;> rfl }
  rw [← Cslib.Probability.PMF.uniformOfFintype_map_equiv e,
    ← Cslib.Probability.PMF.uniformOfFintype_prod]
  simp only [PMF.bind_map, PMF.bind_bind]
  rfl
