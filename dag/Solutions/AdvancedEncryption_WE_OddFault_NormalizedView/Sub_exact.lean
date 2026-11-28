import Mathlib

theorem solution {R ι : Type*} [CommRing R] [Fintype ι]
    (a t e m : R) (w k : ι → R) (hw : ∑ i, w i = 1) :
    ∑ i, w i * (a * (t + k i) + e + m) = a * (t + ∑ i, w i * k i) + e + m := by
  calc
    _ = ∑ i, (a * (w i * k i) + w i * (a * t + e + m)) :=
      Finset.sum_congr rfl fun i _ ↦ by ring
    _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, hw]; ring
