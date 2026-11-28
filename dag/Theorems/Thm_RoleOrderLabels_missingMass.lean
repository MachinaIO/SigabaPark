import Definitions.Def_RoleOrderLabels
import Mathlib.Tactic

theorem RoleOrderLabels.missingMass {J : Type*} [Fintype J] (hits : J → ℝ) (mu : ℝ)
    (moment : (∑ h, (hits h-mu)^2) ≤ Fintype.card J * mu) :
    (∑ h, if hits h = 0 then mu^2 else 0) ≤ Fintype.card J * mu := by
  sorry
