import Mathlib.Tactic

theorem solution {H K R : Type*} [Fintype H] [Fintype K] [AddGroup K] [Semiring R]
    (f g : H → K → R) :
    (∑ h, (∑ x, f h x) * (∑ x, g h x)) =
      ∑ h, ∑ x, ∑ v, f h (x + v) * g h x := by
  apply Finset.sum_congr rfl
  intro h _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [← Finset.sum_mul]
  congr 1
  exact (Fintype.sum_equiv (Equiv.addLeft x) (fun v ↦ f h (x + v)) (f h) (by intro v; rfl)).symm
