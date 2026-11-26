module

public import Definitions.Def_LatticeAttack_Reduction_Rogers_GramAxialIntegration
public import Definitions.Def_LatticeAttack_Reduction_Rogers_GramDensity

set_option autoImplicit true

/-! # [Laa26]'s `ClassicalGramFormula`, discharged

`spherical_gram_formula_all` (the spherical Gram law for every `2 ≤ s`, `s + 2 ≤ n`) and the
transport `classicalGramFormula_volume_of_spherical` give the archive's hypothesis for Lebesgue
measure on every finite-dimensional real inner product space. -/

@[expose] public section
open MeasureTheory

namespace SigabaNeo.Rogers.Gram

theorem classicalGramFormula_volume {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] :
    ClassicalGramFormula (volume : Measure E) :=
  classicalGramFormula_volume_of_spherical fun s hs hn ↦ spherical_gram_formula_all _ s hs hn

end SigabaNeo.Rogers.Gram

#print axioms SigabaNeo.Rogers.Gram.classicalGramFormula_volume
