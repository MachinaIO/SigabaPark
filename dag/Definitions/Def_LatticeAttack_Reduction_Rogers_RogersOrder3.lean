import Definitions.Def_LatticeAttack_Reduction_Rogers_RogersOrder3Assembly
import Definitions.Def_LatticeAttack_Reduction_Rogers_RogersOrder3ReindexSum
import Definitions.Def_LatticeAttack_Reduction_Rogers_RogersOrder3FrameMeasure

set_option autoImplicit true

/-! Rogers' mean value formula of order three (the `k = 3` case of `ClassicalRogersFormula.formula`):
for `n ≥ 4`, an arithmetic fundamental domain of finite Haar mass, and admissible `F`, the mean over
the normalized Haar probability on `SL_n(ℝ)/SL_n(ℤ)` of the sum of `F` over ordered triples of nonzero
lattice vectors equals Rogers' diagram sum with the congruence coefficients. -/

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace SigabaNeo.Rogers

theorem rogers_order_three (n : ℕ) (hn : 3 < n) (D : Set (SL n))
    (hD : IsFundamentalDomain (integerGroup n).op D (groupHaar n)) (hfin : groupHaar n D ≠ ⊤)
    (F : (Fin 3 → E n) → ℝ≥0∞) (hF : Admissible F) :
    (∫⁻ L, tupleWorkload F L ∂domainProbability (groupHaar n) D) =
      diagramSum (congruenceCoefficient n) F :=
  rogers_order_three_of_plane_and_frame n hn D hD hfin F hF
    (rankTwo_reindex n D F) (Frame.rogers_three_frame_measure n hn D hD hfin)

end SigabaNeo.Rogers

#print axioms SigabaNeo.Rogers.rogers_order_three
