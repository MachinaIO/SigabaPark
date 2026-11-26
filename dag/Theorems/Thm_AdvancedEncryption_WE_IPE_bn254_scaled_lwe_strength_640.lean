import SigabaNeoStd.Lattices.LWE
import SigabaNeoStd.Lattices.Estimator.Bound.CbdQ
open SigabaNeo.Lattices.Estimator SigabaNeo.Lattices.Estimator.Fx SigabaNeo.Lattices.Estimator.NumMisc SigabaNeo.Lattices.Estimator.Bkw
open SigabaNeo.Lattices.Estimator.Reduction
open SigabaNeo.Lattices
set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem AdvancedEncryption.WE.IPE.bn254_scaled_lwe_strength_640 : 640 ≤ LWE.H ⟨2^17,2^21,(2^259 * 21888242871839275222246405745257275088548364400416034343698204186575808495617),.cbd 16,.cbd 16,by positivity⟩ := by sorry
