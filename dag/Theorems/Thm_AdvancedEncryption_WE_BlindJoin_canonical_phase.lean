import Mathlib
theorem AdvancedEncryption.WE.BlindJoin.canonical_phase {K I : Type*} [CommRing K] [Fintype I]
    (w H noise mask : I → K) (sk V : K) :
    V - sk*(∑ i, w i*H i) - (∑ i, w i*noise i) =
    (V - ∑ i, w i*(sk*H i+noise i+mask i)) + ∑ i, w i*mask i := by sorry
