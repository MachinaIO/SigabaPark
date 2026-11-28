import Mathlib.Tactic

theorem SyndromePhaseGuard.cosetEnergy {H K R : Type*} [Fintype H] [Fintype K] [AddGroup K] [Semiring R]
    (f g : H → K → R) :
    (∑ h, (∑ x, f h x) * (∑ x, g h x)) =
      ∑ h, ∑ x, ∑ v, f h (x + v) * g h x := by
  sorry
