module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

set_option autoImplicit true

public section

namespace SigabaNeo.Lattices.Attacks.Bkw

open scoped ENNReal

/-- Summing the masses of the disjoint first-acceptance times gives the filtered law. -/
theorem retry_mass_eq_filter {α : Type*} (p : PMF α) (s : Set α)
    (h : ∃ a ∈ s, a ∈ p.support) (x : α) :
    (∑' n : ℕ, (1 - ∑' a, s.indicator p a) ^ n * s.indicator p x) = p.filter s h x := by
  have hle : (∑' a, s.indicator p a) ≤ 1 := by
    rw [← p.tsum_coe]
    exact tsum_le_tsum fun a ↦ Set.indicator_le_self _ _ _
  rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric, PMF.filter_apply, mul_comm]
  congr 2
  exact ENNReal.sub_sub_cancel ENNReal.one_ne_top hle

#print axioms retry_mass_eq_filter

end SigabaNeo.Lattices.Attacks.Bkw
