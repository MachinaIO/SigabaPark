import Definitions.Def_LatticeAttack_Reduction_Rogers_RogersOrderKIntegerDiagram
import Definitions.Def_LatticeAttack_Reduction_Rogers_RogersOrderKFrame

set_option autoImplicit true

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace SigabaNeo.Rogers

/-- Apply the basis of the pivot congruence kernel before reconstructing the tuple. -/
def basisTuple {n r k q} (A : Diagram r k (q+1)) (x : Fin r → E n) : Fin k → E n :=
  diagramTuple A (frameBasisChange n ((diagramBasisMatrix A).map (Int.castRingHom ℝ)) x)

theorem basisTuple_measurable {n r k q} (A : Diagram r k (q+1)) :
    Measurable (@basisTuple n r k q A) := by
  apply Measurable.comp (g := diagramTuple A) (by unfold diagramTuple; fun_prop)
  exact (frameBasisChange _ _).continuous_of_finiteDimensional.measurable

def basisOrbitSum {n k} (D : Set (SL n)) (F : (Fin k → E n) → ℝ≥0∞) (r : Fin k) : ℝ≥0∞ :=
  ∑' q, ∑' A : Diagram (r.val+1) k (q+1), ∑' z : Frame.independent n (r.val+1),
    ∫⁻ g in D, F (basisTuple A (Frame.frameEval z g)) ∂groupHaar n

theorem basisOrbitSum_evaluation {n k} (D : Set (SL n)) (r : Fin k)
    (hm : Frame.frameMeasure (k := r.val+1) D = groupHaar n D • Measure.pi (fun _ ↦ volume))
    (F : (Fin k → E n) → ℝ≥0∞) (hF : Measurable F) :
    basisOrbitSum D F r = groupHaar n D * rankDiagramTerm F r := by
  unfold basisOrbitSum rankDiagramTerm
  rw [← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro q
  rw [← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro A
  refine (Frame.frameMeasure_lintegral D (fun x ↦ F (basisTuple A x)) (hF.comp (basisTuple_measurable A))).symm.trans ?_
  rw [hm,
    lintegral_smul_measure, smul_eq_mul]
  congr 1
  let T := frameBasisChange n ((diagramBasisMatrix A).map (Int.castRingHom ℝ))
  let u := fun x ↦ F (diagramTuple A x)
  have hu : Measurable u := hF.comp (by unfold diagramTuple; fun_prop)
  change (∫⁻ x, u (T x) ∂Measure.pi _) = _ * ∫⁻ x, u x ∂Measure.pi _
  have he : Measure.map T (Measure.pi (fun _ ↦ volume)) =
      congruenceCoefficient n k r q A • Measure.pi (fun _ ↦ volume) :=
    diagramBasisChange_map n k q r A
  rw [← lintegral_map hu T.continuous_of_finiteDimensional.measurable, he, lintegral_smul_measure, smul_eq_mul]

end SigabaNeo.Rogers
