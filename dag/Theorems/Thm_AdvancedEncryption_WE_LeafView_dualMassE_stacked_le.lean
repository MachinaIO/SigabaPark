import SigabaNeoStd.Lattices.Trapdoor.Family.Joint
import Definitions.Def_SuccinctLWE

open Matrix SigabaNeo.Lattices Cslib.Probability AdvancedEncryption.WE.Assumptions.SuccinctLWE
open scoped ENNReal

open Classical in
/-- **Block bound for the smoothness of `Λ^⊥([I_ℓ ⊗ B | W])`.** The lattice contains
`Λ^⊥(B)^ℓ ⊕ Λ^⊥(W)`, so its nonzero dual Gaussian mass (at width `1/τ`) is at most
`(1 + S_B)^ℓ (1 + S_W) − 1`, where `S_M = Σ_{v ≠ 0, v ⊥ ker M} e^{−π τ² ‖v‖²/q²}` is the bound on the
nonzero dual mass of `Λ^⊥(M)` used by `SigabaNeoStd` (`dualMassE_le`). -/
theorem AdvancedEncryption.WE.LeafView.dualMassE_stacked_le {n m q ℓ : ℕ} [NeZero q]
    (B : Matrix (Fin n) (Fin m) (ZMod q)) (W : Matrix (Fin (ℓ * n)) (Fin m) (ZMod q)) (τ : ℝ) :
    dualMassE (stacked B W) τ + 1 ≤
      ((∑' v : Fin m → ℤ, if v ≠ 0 ∧ Orth B v then wt τ q v else 0) + 1) ^ ℓ *
        ((∑' v : Fin m → ℤ, if v ≠ 0 ∧ Orth W v then wt τ q v else 0) + 1) := by sorry
