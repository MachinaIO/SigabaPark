import Definitions.Def_WE_EncryptorSetup

open Matrix SigabaNeo.Lattices Cslib.Probability AdvancedEncryption.WE.Assumptions.SuccinctLWE
  AdvancedEncryption.WE.EncryptorSetup
open scoped ENNReal

theorem AdvancedEncryption.WE.LeafView.challenge_none_le_setup_error (p : Params) (mb : ℕ) (hm : mb + p.ℓ * p.n * p.k = p.m)
    (hσ : (0 : ℝ) < p.σ) (ε : ℝ≥0∞) (h : CloseTo (encLaw p mb hm hσ) (chalLaw p) ε) :
    (chalLaw p).toOuterMeasure {x | x.2.2 = none} ≤ ε := by
  sorry
