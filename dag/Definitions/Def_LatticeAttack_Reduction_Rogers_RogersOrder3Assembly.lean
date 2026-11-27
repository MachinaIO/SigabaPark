import Definitions.Def_LatticeAttack_Reduction_Rogers_RogersOrderKLineParam
import Definitions.Def_LatticeAttack_Reduction_Rogers_RogersOrderKShear
import Definitions.Def_LatticeAttack_Reduction_Rogers_RogersOrder3Planes

set_option autoImplicit true

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace SigabaNeo.Rogers

/-- A normalized independent-frame measure evaluates the last rank at every order. -/
theorem rankLast_of_frame_measure {n k} (D : Set (SL n))
    (hm : Frame.frameMeasure (k := k+1) D = groupHaar n D • Measure.pi (fun _ ↦ volume))
    (F : (Fin (k+1) → E n) → ℝ≥0∞) (hF : Measurable F) :
    rankOrbitSum (Nat.succ_pos k) D F (Fin.last k) =
      groupHaar n D * rankDiagramTerm F (Fin.last k) := by
  rw [Frame.rankOrbitSum_last D F hF, hm, lintegral_smul_measure, smul_eq_mul,
    rankDiagramTerm_last]

theorem rogers_order_three_of_plane_and_frame (n : ℕ) (hn : 3 < n) (D : Set (SL n))
    (hd : IsFundamentalDomain (integerGroup n).op D (groupHaar n)) (hfin : groupHaar n D ≠ ⊤)
    (F : (Fin 3 → E n) → ℝ≥0∞) (hF : Admissible F)
    (hplane : rankOrbitSum (by decide) D F 1 = planeOrbitSum D F)
    (hframe : Frame.frameMeasure (k := 3) D = groupHaar n D • Measure.pi (fun _ ↦ volume)) :
    (∫⁻ L, tupleWorkload F L ∂domainProbability (groupHaar n) D) =
      diagramSum (congruenceCoefficient n) F := by
  apply rogers_of_rank_terms (by decide) D hd hfin F hF.1
  intro r
  fin_cases r
  · exact rankOne_evaluation n 2 (by omega) D hd hfin F hF.1
  · exact hplane.trans (planeOrbitSum_evaluation (by omega) hd hfin F hF.1)
  · exact rankLast_of_frame_measure (k := 2) D hframe F hF.1

end SigabaNeo.Rogers
