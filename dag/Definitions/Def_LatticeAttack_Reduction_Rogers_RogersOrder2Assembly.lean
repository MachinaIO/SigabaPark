import Definitions.Def_LatticeAttack_Reduction_Rogers_RogersOrder2Param

set_option autoImplicit true

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace SigabaNeo.Rogers

theorem orderTwo_dependent (n : ℕ) (hn : 2 < n) (D : Set (SL n))
    (hD : IsFundamentalDomain (integerGroup n).op D (groupHaar n)) (hfin : groupHaar n D ≠ ⊤)
    (F : (Fin 2 → E n) → ℝ≥0∞) (hf : Measurable F) :
    (∑' z : ↥((orderTwoIndependent n)ᶜ), orderTwoOrbit D F z.val) =
      groupHaar n D * orderTwoRankTerm F 0 :=
  (orderTwo_line_reindex n D F).trans (orderTwo_siegel_lines n hn D hD hfin F hf)

/-- Evaluation of the independent-pair orbit sum suffices for the full second moment. -/
theorem orderTwo_of_independent (n : ℕ) (hn : 2 < n) (D : Set (SL n))
    (hD : IsFundamentalDomain (integerGroup n).op D (groupHaar n)) (hfin : groupHaar n D ≠ ⊤)
    (F : (Fin 2 → E n) → ℝ≥0∞) (hf : Measurable F)
    (hind : (∑' z : orderTwoIndependent n, orderTwoOrbit D F z.val) =
      groupHaar n D * ∫⁻ v, F v ∂Measure.pi (fun _ ↦ volume)) :
    (∫⁻ L, tupleWorkload F L ∂domainProbability (groupHaar n) D) =
      diagramSum (congruenceCoefficient n) F := by
  let := groupHaar_rightInvariant n
  obtain ⟨S, _, _, hS⟩ := arithmetic_domain n
  have hμ : groupHaar n ≠ 0 := fun h ↦ hS (by rw [h]; rfl)
  rw [orderTwo_domain_split D F hf, orderTwo_dependent n hn D hD hfin F hf, hind,
    ← orderTwo_fullRank n F, ← mul_add, ← mul_assoc,
    ENNReal.inv_mul_cancel (domain_mass_ne_zero _ hμ hD) hfin, one_mul]
  exact (Fin.sum_univ_two (orderTwoRankTerm F)).symm

#print axioms orderTwo_dependent
#print axioms orderTwo_of_independent

end SigabaNeo.Rogers
