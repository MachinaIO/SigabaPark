import Definitions.Def_LatticeAttack_Reduction_Rogers_SiegelAssemblyDomain
import Definitions.Def_LatticeAttack_Reduction_Rogers_SiegelAssemblyUnfolding
import Definitions.Def_LatticeAttack_Reduction_Rogers_SiegelOrbitEvaluation

set_option autoImplicit true

open MeasureTheory SigabaNeo.Rogers
open scoped ENNReal

theorem siegel_mean_value (n : ℕ) (hn : 2 ≤ n) :
    ∃ D : Set (SL n), MeasurableSet D ∧
      IsFundamentalDomain (integerGroup n).op D (groupHaar n) ∧
      IsProbabilityMeasure (domainProbability (groupHaar n) D) ∧
      SMulInvariantMeasure (SL n) (LatticeSpace n) (domainProbability (groupHaar n) D) ∧
      ∀ f : E n → ℝ≥0∞, Measurable f →
        (∫⁻ L, tupleWorkload (fun v : Fin 1 → E n ↦ f (v 0)) L
          ∂domainProbability (groupHaar n) D) = ∫⁻ x, f x :=
  siegel_mean_value_of_evaluation n (open_arithmetic_domain_finite_mass n hn)
    (siegel_domain_unfolding_evaluation n hn)

#print axioms siegel_mean_value
