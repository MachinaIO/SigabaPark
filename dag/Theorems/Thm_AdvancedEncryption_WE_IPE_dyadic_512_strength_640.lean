import SigabaNeoStd.Lattices.LWE
import SigabaNeoStd.Lattices.Estimator.Bound.CbdQ
open SigabaNeo.Lattices.Estimator SigabaNeo.Lattices.Estimator.Fx SigabaNeo.Lattices.Estimator.NumMisc SigabaNeo.Lattices.Estimator.Bkw
open SigabaNeo.Lattices.Estimator.Reduction
open SigabaNeo.Lattices
theorem AdvancedEncryption.WE.IPE.dyadic_512_strength_640 : 640 ≤ LWE.H ⟨2^17,2^21,2^512,.cbd 16,.cbd 16,by positivity⟩ := by
  sorry
