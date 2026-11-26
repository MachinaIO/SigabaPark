import Definitions.Def_WE_EncryptorSetup

open Matrix SigabaNeo.Lattices Cslib.Probability AdvancedEncryption.WE.Assumptions.SuccinctLWE
  AdvancedEncryption.WE.EncryptorSetup
open scoped ENNReal

theorem encryptor_present (p : Params) (mb : ℕ) (hm : mb + p.ℓ * p.n * p.k = p.m)
    (hσ : (0 : ℝ) < p.σ) : (encLaw p mb hm hσ).toOuterMeasure {x | x.2.2 = none} = 0 := by
  rw [PMF.toOuterMeasure_apply_eq_zero_iff, Set.disjoint_left]
  intro x hxS hx
  simp only [encLaw, PMF.mem_support_bind_iff, PMF.support_map, Set.mem_image] at hxS
  obtain ⟨B, _, A, _, Rc, _, T, hT, rfl⟩ := hxS
  change T = none at hx
  subst T
  simp only [floodT, PMF.support_map, Set.mem_image] at hT
  obtain ⟨o, ho, he⟩ := hT
  cases o with
  | none =>
    have h := support_sampleOptList _ none ho
    simp at h
  | some l => cases he

theorem solution (p : Params) (mb : ℕ) (hm : mb + p.ℓ * p.n * p.k = p.m)
    (hσ : (0 : ℝ) < p.σ) (ε : ℝ≥0∞) (h : CloseTo (encLaw p mb hm hσ) (chalLaw p) ε) :
    (chalLaw p).toOuterMeasure {x | x.2.2 = none} ≤ ε := by
  simpa only [encryptor_present p mb hm hσ, zero_add] using h.symm {x | x.2.2 = none}
