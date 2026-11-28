import Definitions.Def_RoleOrderLabels
import Mathlib.Tactic

theorem solution {J : Type*} [Fintype J] (hits : J → ℝ) (mu : ℝ)
    (moment : (∑ h, (hits h-mu)^2) ≤ Fintype.card J * mu) :
    (∑ h, if hits h = 0 then mu^2 else 0) ≤ Fintype.card J * mu := by
  classical
  apply le_trans (Finset.sum_le_sum (s := Finset.univ) (g := fun h => (hits h-mu)^2) ?_) moment
  intro h _
  by_cases hz : hits h = 0
  · simp [hz]
  · simp [hz, sq_nonneg]
