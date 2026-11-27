import Mathlib
theorem solution {K I : Type*} [CommRing K] [Fintype I]
    (w H noise mask : I → K) (sk V : K) :
    V - sk*(∑ i, w i*H i) - (∑ i, w i*noise i) =
    (V - ∑ i, w i*(sk*H i+noise i+mask i)) + ∑ i, w i*mask i := by
  simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  have h (i : I) : sk*(w i*H i) = w i*(sk*H i) := by ring
  simp_rw [h]
  abel
