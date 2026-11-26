import Definitions.Def_WE_MaskedGGH15

open Matrix SigabaNeo SigabaNeo.Lattices AdvancedEncryption.WE.GGH15 AdvancedEncryption.WE.MaskedGGH15

/-- **CVW18 Construction 6.4**: the subset product of the CNF branching program vanishes exactly
on the satisfying assignments, `M_x = 0 ⟺ Ψ(x) = 1`. -/
theorem AdvancedEncryption.WE.MaskedGGH15.cnfMat_pathProd_eq_zero_iff {w h : ℕ} (Ψ : CNF w h) (x : Fin h → Bool) :
    pathProd (cnfMat Ψ) x = 0 ↔ Sat Ψ x := by sorry
