import SigabaNeoStd.Lattices.LWE
import SigabaNeoStd.Lattices.Estimator.Bound.CbdQ
open SigabaNeo.Lattices.Estimator SigabaNeo.Lattices.Estimator.Fx SigabaNeo.Lattices.Estimator.NumMisc SigabaNeo.Lattices.Estimator.Bkw
open SigabaNeo.Lattices.Estimator.Reduction
open SigabaNeo.Lattices
theorem AdvancedEncryption.WE.IPE.dyadic_estimator_ge {n q e M M₀ kb W ZA K₀ R : ℕ} {lq : Fx} (hq : 2 ^ e ≤ q)
    (he : 512 ≤ e) (hlq : log2Nat q = lq) (hl2q : log2 (ofInt (q : ℤ)) = lq) (hM₀ : M₀ ≤ M)
    (hMlo : maxBeta + 1 + W + (kb + 22) ≤ M + n) (hMhi : 56 * M ≤ (n - ZA) * R ^ 6)
    (hf : cbdFactsQ n kb W ZA K₀ R = true)
    (hc : ∀ b < maxBeta + 2, cbdCheckQ n lq M₀ kb W b = true) :
    kb ≤ estimatorBits (cbdPq n q M) := by
  sorry
