import Definitions.Def_LatticeAttack_Research_Wall1_MarkedIntegerSection
import Mathlib.Probability.Distributions.Uniform

set_option autoImplicit true

/-! # Uniform shortest representatives in a finite group of marks -/

noncomputable section

namespace SigabaNeo.Wall1

open Submodule MeasureTheory Metric
open scoped ENNReal
variable {V : Type*} [NormedAddCommGroup V] (L : Submodule ℤ V)

/-- A shortest lift in a coset, allowing any fixed resolution of ties. -/
def IsShortestMarkLift (h : V ⧸ L) (x : V) : Prop :=
  L.mkQ x = h ∧ ∀ y, L.mkQ y = h → ‖x‖ ≤ ‖y‖

theorem exists_shortestMarkLift [ProperSpace V] [DiscreteTopology L] (h : V ⧸ L) :
    ∃ x, IsShortestMarkLift L h x := by
  obtain ⟨a, rfl⟩ := L.mkQ_surjective h
  have : DiscreteTopology L.toAddSubgroup := ‹_›
  have hc : IsClosed (L : Set V) := L.toAddSubgroup.isClosed_of_discreteTopology
  obtain ⟨b, hb, hmin⟩ := hc.exists_infDist_eq_dist ⟨0, L.zero_mem⟩ a
  have hb0 : L.mkQ b = 0 := (Submodule.Quotient.mk_eq_zero L).2 hb
  refine ⟨a - b, by rw [map_sub, hb0, sub_zero], fun y hy ↦ ?_⟩
  have hmem : a - y ∈ L := (Submodule.Quotient.mk_eq_zero L).1
    (show L.mkQ (a-y) = 0 by rw [map_sub, hy, sub_self])
  have hle := infDist_le_dist_of_mem (x := a) hmem
  simpa [hmin, dist_eq_norm] using hle

variable {H : AddSubgroup (V ⧸ L)} {σ : H → V}

/-- Any fixed shortest section has distinct representatives in the closed Voronoi cell. -/
theorem shortestMarkLift_geometry (hσ : ∀ h, IsShortestMarkLift L h.val (σ h)) :
    Function.Injective σ ∧ ∀ h (l : L), ‖σ h‖ ≤ ‖σ h - l.val‖ := by
  constructor
  · intro a b he
    exact Subtype.ext ((hσ a).1.symm.trans ((congrArg L.mkQ he).trans (hσ b).1))
  · intro h l
    apply (hσ h).2
    rw [map_sub, (hσ h).1, show L.mkQ l.val = 0 from (Submodule.Quotient.mk_eq_zero L).2 l.2,
      sub_zero]

/-- Pushforward of the uniform law on any finite set of marks, including a restriction
to the marks giving a specified winner type, with the identical tie rule throughout. -/
theorem shortestMarkLift_uniform [MeasurableSpace V] [MeasurableSpace H]
    [MeasurableSingletonClass H] [Finite H] (s : Finset H)
    (hσ : ∀ h, IsShortestMarkLift L h.val (σ h)) :
    Measure.map σ (Measure.uniformOfFinset s) =
      Measure.uniformOfFinset (s.map ⟨σ, (shortestMarkLift_geometry L hσ).1⟩) := by
  classical
  have hm : Measurable σ := measurable_of_countable _
  simp only [Measure.uniformOfFinset, Finset.card_map, Finset.sum_map, Function.Embedding.coeFn_mk]
  rw [Measure.map_finset_sum hm.aemeasurable]
  apply Finset.sum_congr rfl
  intro i _
  change Measure.map σ ((s.card : ℝ≥0∞)⁻¹ • Measure.dirac i) = _
  rw [Measure.map_smul, Measure.map_dirac' hm]
  exact hm.aemeasurable

end SigabaNeo.Wall1

#print axioms SigabaNeo.Wall1.exists_shortestMarkLift
#print axioms SigabaNeo.Wall1.shortestMarkLift_geometry
#print axioms SigabaNeo.Wall1.shortestMarkLift_uniform
