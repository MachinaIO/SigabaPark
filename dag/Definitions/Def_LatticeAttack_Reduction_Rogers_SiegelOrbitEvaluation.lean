module

public import Definitions.Def_LatticeAttack_Reduction_Rogers_MeanValue

set_option autoImplicit true

@[expose] public section

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace SigabaNeo.Rogers

abbrev NonzeroIntVector (n : ℕ) := {z : Fin n → ℤ // z ≠ 0}

/-- Content one selects the primitive integer vectors. -/
def vectorContent {n : ℕ} (z : NonzeroIntVector n) : ℕ :=
  Finset.univ.gcd fun i ↦ (z.val i).natAbs

def vectorOrbitalIntegral {n : ℕ} (D : Set (SL n)) (f : E n → ℝ≥0∞)
    (z : NonzeroIntVector n) : ℝ≥0∞ :=
  ∫⁻ g in D, f (WithLp.toLp 2 (g • fun j ↦ (z.val j : ℝ))) ∂groupHaar n

/-- Expand the Siegel transform, then group its orbital integrals by content. -/
theorem siegel_integral_by_content {n : ℕ} (D : Set (SL n)) (f : E n → ℝ≥0∞)
    (hf : Measurable f) :
    (∫⁻ g in D, tupleWorkload (fun v : Fin 1 → E n ↦ f (v 0))
      (QuotientGroup.mk g) ∂groupHaar n) =
      ∑' c : ℕ, ∑' z : {z : NonzeroIntVector n // vectorContent z = c},
        vectorOrbitalIntegral D f z.val := by
  refine (domain_lintegral_tupleWorkload (groupHaar n) D
    (F := fun v : Fin 1 → E n ↦ f (v 0)) (hf.comp (measurable_pi_apply 0))).trans ?_
  exact ((Equiv.funUnique (Fin 1) (NonzeroIntVector n)).tsum_eq
    (vectorOrbitalIntegral D f)).trans (tsum_fiberwise _ _).symm

#print axioms siegel_integral_by_content

/-- Normalize a finite arithmetic domain once the domain unfolding has been evaluated. -/
theorem siegel_mean_value_of_evaluation (n : ℕ)
    (mass : ∃ D : Set (SL n), MeasurableSet D ∧
      IsFundamentalDomain (integerGroup n).op D (groupHaar n) ∧
      groupHaar n D ≠ 0 ∧ groupHaar n D ≠ ⊤)
    (unfolding : ∀ (D : Set (SL n)), MeasurableSet D →
      IsFundamentalDomain (integerGroup n).op D (groupHaar n) → groupHaar n D ≠ ⊤ →
      ∀ (f : E n → ℝ≥0∞), Measurable f →
        (∫⁻ g in D, tupleWorkload (fun v : Fin 1 → E n ↦ f (v 0))
          (QuotientGroup.mk g) ∂groupHaar n) = groupHaar n D * ∫⁻ x, f x) :
    ∃ D : Set (SL n), MeasurableSet D ∧ IsFundamentalDomain (integerGroup n).op D (groupHaar n) ∧
      IsProbabilityMeasure (domainProbability (groupHaar n) D) ∧
      SMulInvariantMeasure (SL n) (LatticeSpace n) (domainProbability (groupHaar n) D) ∧
      ∀ f : E n → ℝ≥0∞, Measurable f →
        (∫⁻ L, tupleWorkload (fun v : Fin 1 → E n ↦ f (v 0)) L
          ∂domainProbability (groupHaar n) D) = ∫⁻ x, f x := by
  obtain ⟨D, hm, hd, hp, hfin⟩ := mass
  let := groupHaar_rightInvariant n
  let : BorelSpace (SL n) := ⟨rfl⟩
  let : LocallyCompactSpace (Matrix (Fin n) (Fin n) ℝ) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → ℝ))
  let : LocallyCompactSpace (SL n) :=
    Matrix.SpecialLinearGroup.isClosedEmbedding_val.locallyCompactSpace
  let : (groupHaar n).IsMulLeftInvariant :=
    inferInstanceAs (Measure.haar : Measure (SL n)).IsMulLeftInvariant
  refine ⟨D, hm, hd, domainProbability_probability _ _ hp hfin,
    domainProbability_invariant _ hd, ?_⟩
  intro f hf
  exact siegel_of_domain_unfolding _ _ hp hfin f
    (tupleWorkload_measurable (hf.comp (measurable_pi_apply 0)))
    (unfolding D hm hd hfin f hf)

#print axioms siegel_mean_value_of_evaluation

end SigabaNeo.Rogers
