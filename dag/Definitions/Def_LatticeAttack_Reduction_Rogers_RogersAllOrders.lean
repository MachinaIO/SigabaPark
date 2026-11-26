import Definitions.Def_LatticeAttack_Reduction_Rogers_RogersAllOrdersExistence
import Definitions.Def_LatticeAttack_Reduction_Rogers_RogersAllOrdersFrame

set_option autoImplicit true

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace SigabaNeo.Rogers

/-- Rogers' formula at every order below the dimension for a finite-mass fundamental domain. -/
theorem rogers_formula_domain {n : ℕ} (D : Set (SL n))
    (hd : IsFundamentalDomain (integerGroup n).op D (groupHaar n)) (hf : groupHaar n D ≠ ⊤) :
    ClassicalRogersFormula (domainProbability (groupHaar n) D) (congruenceCoefficient n) := by
  apply (classicalRogersFormula_iff _).2
  intro k hk hkn F hF
  obtain ⟨t,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  apply rogers_of_rank_terms hk D hd hf F hF.1
  intro r
  rw [rank_reindex_of_normalForm r D F (fun z hz ↦ AllOrders.hasDiagram_succ z hz)]
  exact basisOrbitSum_evaluation D r
    (Frame.rogers_frame_measure n (r.val+1) (Nat.succ_pos _) (by have := r.isLt; omega) D hd hf)
    F hF.1

/-- The normalized Haar probability on the lattice quotient satisfies the classical diagram
formula with the explicit congruence coefficients, simultaneously for all orders. -/
theorem rogers_formula_all (n : ℕ) (hn : 2 ≤ n) :
    ∃ D : Set (SL n), MeasurableSet D ∧
      IsFundamentalDomain (integerGroup n).op D (groupHaar n) ∧
      groupHaar n D ≠ 0 ∧ groupHaar n D ≠ ⊤ ∧
      IsProbabilityMeasure (domainProbability (groupHaar n) D) ∧
      SMulInvariantMeasure (SL n) (LatticeSpace n) (domainProbability (groupHaar n) D) ∧
      ClassicalRogersFormula (domainProbability (groupHaar n) D) (congruenceCoefficient n) := by
  obtain ⟨D, hm, hd, hp, hf⟩ := open_arithmetic_domain_finite_mass n hn
  let := groupHaar_rightInvariant n
  let : BorelSpace (SL n) := ⟨rfl⟩
  let : LocallyCompactSpace (Matrix (Fin n) (Fin n) ℝ) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → ℝ))
  let : LocallyCompactSpace (SL n) :=
    Matrix.SpecialLinearGroup.isClosedEmbedding_val.locallyCompactSpace
  let : (groupHaar n).IsMulLeftInvariant :=
    inferInstanceAs (Measure.haar : Measure (SL n)).IsMulLeftInvariant
  exact ⟨D, hm, hd, hp, hf, domainProbability_probability _ _ hp hf,
    domainProbability_invariant _ hd, rogers_formula_domain D hd hf⟩

#print axioms rogers_formula_domain
#print axioms rogers_formula_all

end SigabaNeo.Rogers
