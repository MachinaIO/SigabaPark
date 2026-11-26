module

public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Definitions.Def_LatticeAttack_Reduction_Search_ProductRecall

set_option autoImplicit true

public section

namespace SigabaNeo.Lattices.Search

open MeasureTheory
open scoped ENNReal

/-- Miss probability over all indexed pairs of a fixed ideal transcript. -/
theorem transcriptMiss_le {Ω ι : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (pairs : Finset ι) (miss : ι → Set Ω) (ε : ℝ≥0∞)
    (h : ∀ i ∈ pairs, μ (miss i) ≤ ε) :
    μ (⋃ i ∈ pairs, miss i) ≤ pairs.card • ε := by
  calc
    _ ≤ ∑ i ∈ pairs, μ (miss i) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _i ∈ pairs, ε := Finset.sum_le_sum h
    _ = _ := Finset.sum_const ε

#print axioms transcriptMiss_le

end SigabaNeo.Lattices.Search
