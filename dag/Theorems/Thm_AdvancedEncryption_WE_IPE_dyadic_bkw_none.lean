import SigabaNeoStd.Lattices.LWE
import SigabaNeoStd.Lattices.Estimator.Bound.CbdQ
open SigabaNeo.Lattices.Estimator SigabaNeo.Lattices.Estimator.Fx SigabaNeo.Lattices.Estimator.NumMisc SigabaNeo.Lattices.Estimator.Bkw
open SigabaNeo.Lattices.Estimator.Reduction
open SigabaNeo.Lattices
theorem AdvancedEncryption.WE.IPE.dyadic_bkw_none {p : LWEParams} {e : ℕ} (hq : 2 ^ e ≤ p.q) (he : 512 ≤ e)
    (hs : ¬ p.normalize.Xs.stddev > p.normalize.Xe.stddev) (hz : 0 ≤ zOf p.normalize)
    (herf : Bkw.erf (div (zOf p.normalize) (Fx.sqrt (2 * p.normalize.Xe.stddev))) = ONE) :
    Bkw.cost p = none := by
  sorry
