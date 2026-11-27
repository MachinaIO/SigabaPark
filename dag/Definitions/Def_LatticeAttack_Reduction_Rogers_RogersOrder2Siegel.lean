import Definitions.Def_LatticeAttack_Reduction_Rogers_RogersOrder2Lines
import Definitions.Def_LatticeAttack_Reduction_Rogers_SiegelAssemblyUnfolding

set_option autoImplicit true

noncomputable section
open MeasureTheory
open scoped ENNReal Pointwise
namespace SigabaNeo.Rogers

/-- Apply the order-one unfolding separately to each reduced rational line. -/
theorem orderTwo_siegel_lines (n : ℕ) (hn : 2 < n) (D : Set (SL n))
    (hD : IsFundamentalDomain (integerGroup n).op D (groupHaar n)) (hfin : groupHaar n D ≠ ⊤)
    (F : (Fin 2 → E n) → ℝ≥0∞) (hf : Measurable F) :
    (∑' q, ∑' A : Diagram 1 2 (q+1), ∑' z : NonzeroIntVector n,
      vectorOrbitalIntegral D (fun x ↦ F (orderTwoLine A x)) z) =
      groupHaar n D * orderTwoRankTerm F 0 := by
  let := groupHaar_rightInvariant n
  let : BorelSpace (SL n) := ⟨rfl⟩
  obtain ⟨T, hsub, hm, he⟩ := hD.nullMeasurableSet.exists_measurable_superset_ae_eq
  have ht : IsFundamentalDomain (integerGroup n).op T (groupHaar n) := {
    nullMeasurableSet := hm.nullMeasurableSet
    ae_covers := hD.ae_covers.mono fun _ ⟨g,hg⟩ ↦ ⟨g,hsub hg⟩
    aedisjoint := by
      intro a b hab
      exact (hD.aedisjoint hab).congr ((smul_set_ae_eq a.val).mpr he)
        ((smul_set_ae_eq b.val).mpr he) }
  rw [orderTwo_rank_one n F hf, ← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro q
  rw [← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro A
  let u := fun x : E n ↦ F (orderTwoLine A x)
  have hu : Measurable u := hf.comp (Measurable.of_eval fun j ↦ measurable_const_smul _)
  have horb := (domain_lintegral_tupleWorkload (groupHaar n) D
    (F := fun v : Fin 1 → E n ↦ u (v 0)) (hu.comp (measurable_pi_apply 0))).trans
    ((Equiv.funUnique (Fin 1) (NonzeroIntVector n)).tsum_eq (vectorOrbitalIntegral D u))
  refine horb.symm.trans ?_
  rw [← Measure.restrict_congr_set he, ← measure_congr he]
  exact siegel_domain_unfolding_evaluation n (by omega) T hm ht
    (by simpa only [measure_congr he] using hfin) u hu

end SigabaNeo.Rogers
