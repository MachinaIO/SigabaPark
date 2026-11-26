import SigabaNeoStd.Lattices.Trapdoor.Family.Joint
import SigabaNeoStd.Lattices.Trapdoor.Family.Close
import Definitions.Def_WE_EncryptorSetup

open Matrix SigabaNeo.Lattices Cslib.Probability AdvancedEncryption.WE.Assumptions.SuccinctLWE
  AdvancedEncryption.WE.EncryptorSetup
open scoped ENNReal

theorem AdvancedEncryption.WE.LeafView.encryptor_leafGood_failure (p : Params) (mb : ℕ) (hm : mb + p.ℓ * p.n * p.k = p.m)
    (hσ : (0 : ℝ) < p.σ) (h1 : (1 : ℝ) ≤ p.σ) (hM : 0 < p.ℓ * p.m + p.m)
    (E : ℕ) (hE : (p.σ : ℝ) * Real.sqrt (p.ℓ * p.m + p.m : ℕ) + (p.ℓ * p.n * p.k : ℕ) ≤ E) :
    (encLaw p mb hm hσ).toOuterMeasure {x | ¬ leafGood E x.2.2} ≤
      (p.ℓ * (p.n * p.k) : ℕ) * ((p.ℓ * p.m + p.m : ℕ) *
        ENNReal.ofReal (6 * (1 / 4) ^ (p.ℓ * p.m + p.m))) := by
  sorry
