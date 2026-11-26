module

public import Definitions.Def_LatticeAttack_Research_Wall2_Incidence
public import Definitions.Def_LatticeAttack_Research_Wall2_Adaptive
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

set_option autoImplicit true

public section

namespace SigabaNeo.Wall2

/-- A single signed pair exceeds the mass budget at every width up to R. -/
theorem dualPair_exceeds {s R a c ε : ℝ} (hs : 0 ≤ s) (hsR : s ≤ R)
    (hε : ε < 2 * Real.exp (-c))
    (hRa : Real.pi * (R * a) ^ 2 ≤ c) :
    ε < 2 * Real.exp (-(Real.pi * (s * a) ^ 2)) := by
  have hs2 : s ^ 2 ≤ R ^ 2 := by nlinarith [mul_nonneg (sub_nonneg.mpr hsR) hs]
  have h := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right hs2 (sq_nonneg a)) Real.pi_pos.le
  rw [mul_pow] at hRa ⊢
  exact hε.trans_le (mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (neg_le_neg (h.trans hRa))) (by norm_num))

#print axioms dualPair_exceeds

end SigabaNeo.Wall2
