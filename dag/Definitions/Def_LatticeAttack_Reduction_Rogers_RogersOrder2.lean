import Definitions.Def_LatticeAttack_Reduction_Rogers_RogersOrder2Assembly
import Definitions.Def_LatticeAttack_Reduction_Rogers_RogersOrder2IndepUniqueness

set_option autoImplicit true

/-! Rogers' mean value formula of order two (the `k = 2` case of `ClassicalRogersFormula.formula`):
for `n ≥ 3`, an arithmetic fundamental domain of finite Haar mass, and admissible `F`, the mean over
the normalized Haar probability on `SL_n(ℝ)/SL_n(ℤ)` of the sum of `F` over ordered pairs of nonzero
lattice vectors equals Rogers' diagram sum with the congruence coefficients. -/

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace SigabaNeo.Rogers

theorem rogers_order_two (n : ℕ) (hn : 2 < n) (D : Set (SL n))
    (hD : IsFundamentalDomain (integerGroup n).op D (groupHaar n)) (hfin : groupHaar n D ≠ ⊤)
    (F : (Fin 2 → E n) → ℝ≥0∞) (hF : Admissible F) :
    (∫⁻ L, tupleWorkload F L ∂domainProbability (groupHaar n) D) =
      diagramSum (congruenceCoefficient n) F :=
  orderTwo_of_independent n hn D hD hfin F hF.1 (rogers_two_independent n hn D hD hfin F hF)

end SigabaNeo.Rogers

#print axioms SigabaNeo.Rogers.rogers_order_two
