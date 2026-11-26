import SigabaNeoStd.Lattices.LWE
import SigabaNeoStd.Lattices.Estimator.Bound.CbdQ

open SigabaNeo.Lattices SigabaNeo.Lattices.Estimator SigabaNeo.Lattices.Estimator.Fx

theorem AdvancedEncryption.WE.IPE.ordinary_cbd16_strength_640 : 640 ≤ LWE.H ⟨2^18,2^22,2^1024,.cbd 16,.cbd 16,by positivity⟩ := by
  sorry
