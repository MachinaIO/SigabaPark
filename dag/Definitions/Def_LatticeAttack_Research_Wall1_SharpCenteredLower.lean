import Definitions.Def_LatticeAttack_Research_Wall1_SharpBallLower
import Definitions.Def_LatticeAttack_Research_Wall1_CenteredBallExclusion

set_option autoImplicit true

/-! Sharp full-ball count with the existing centered-coordinate exclusions. -/
noncomputable section
namespace SigabaNeo.Wall1.RawBallRounding

/-- The explicit volume lower bound for centered integer candidates. -/
theorem centeredLifts_two_coordinate_lower {n : ℕ} {R a : ℝ}
    (hR : 1690 ≤ R) (ha : 0 ≤ a) (ha2 : a^2 = R^2 - (n : ℝ)/4) :
    unitVolume (n+2) * a^(n+2) -
      (Real.pi / Real.sqrt 2) * (unitVolume (n+1) * a^(n+1)) -
      4*(n+2)*Real.sqrt (R^2 - 1664^2 + ((n+2 : ℕ) : ℝ)/4)^ (n+2) * unitVolume (n+2) ≤
      ((centeredLifts (n+2) R).card : ℝ) := by
  have hfull := closedLifts_two_coordinate_lower (by linarith : 0 ≤ R) ha ha2
  have hcenter := centeredLifts_lower_from_full (n+2) hR
  push_cast at hcenter ⊢
  linarith

end SigabaNeo.Wall1.RawBallRounding
#print axioms SigabaNeo.Wall1.RawBallRounding.centeredLifts_two_coordinate_lower
