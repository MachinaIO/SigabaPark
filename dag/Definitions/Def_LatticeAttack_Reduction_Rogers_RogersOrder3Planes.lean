import Definitions.Def_LatticeAttack_Reduction_Rogers_RogersOrderKIntegerDiagram
import Definitions.Def_LatticeAttack_Reduction_Rogers_RogersOrder2

set_option autoImplicit true

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace SigabaNeo.Rogers

/-- Apply the basis of the pivot congruence kernel before reconstructing the triple. -/
def planeTuple {n q} (A : Diagram 2 3 (q+1)) (x : Fin 2 → E n) : Fin 3 → E n :=
  diagramTuple A (frameBasisChange n ((diagramBasisMatrix A).map (Int.castRingHom ℝ)) x)

theorem planeTuple_measurable {n q} (A : Diagram 2 3 (q+1)) :
    Measurable (@planeTuple n q A) := by
  apply Measurable.comp (g := diagramTuple A) (by unfold diagramTuple; fun_prop)
  exact (frameBasisChange _ _).continuous_of_finiteDimensional.measurable

def planeOrbitSum {n} (D : Set (SL n)) (F : (Fin 3 → E n) → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' q, ∑' A : Diagram 2 3 (q+1), ∑' z : orderTwoIndependent n,
    orderTwoOrbit D (fun x ↦ F (planeTuple A x)) z.val

theorem planeOrbitSum_evaluation {n} (hn : 2 < n) {D : Set (SL n)}
    (hd : IsFundamentalDomain (integerGroup n).op D (groupHaar n)) (hfin : groupHaar n D ≠ ⊤)
    (F : (Fin 3 → E n) → ℝ≥0∞) (hF : Measurable F) :
    planeOrbitSum D F = groupHaar n D * rankDiagramTerm F 1 := by
  obtain ⟨C,hC⟩ := independentPairMeasure_proportional hn hd hfin
  have hc := independentPairMeasure_scalar_calibration hn hd hfin hC
  subst C
  unfold planeOrbitSum rankDiagramTerm
  simp only [Fin.val_one, Nat.reduceAdd]
  rw [← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro q
  rw [← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro A
  refine (independentPairMeasure_lintegral D (fun x ↦ F (planeTuple A x)) (hF.comp (planeTuple_measurable A))).symm.trans ?_
  rw [hC,
    lintegral_smul_measure, smul_eq_mul]
  congr 1
  let T := frameBasisChange n ((diagramBasisMatrix A).map (Int.castRingHom ℝ))
  let u := fun x ↦ F (diagramTuple A x)
  have hu : Measurable u := hF.comp (by unfold diagramTuple; fun_prop)
  change (∫⁻ x, u (T x) ∂Measure.pi _) = _ * ∫⁻ x, u x ∂Measure.pi _
  have he : Measure.map T (Measure.pi (fun _ ↦ volume)) =
      congruenceCoefficient n 3 1 q A • Measure.pi (fun _ ↦ volume) :=
    diagramBasisChange_map n 3 q (1 : Fin 3) A
  rw [← lintegral_map hu T.continuous_of_finiteDimensional.measurable, he, lintegral_smul_measure, smul_eq_mul]

end SigabaNeo.Rogers
