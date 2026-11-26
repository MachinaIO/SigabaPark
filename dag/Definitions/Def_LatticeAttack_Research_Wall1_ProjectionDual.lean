import Definitions.Def_LatticeAttack_Research_Wall1_QuotientMinimum
import CslibFrontier.Foundations.Analysis.Lattice.Dual

set_option autoImplicit true

/-! # Orthogonal projections of integer lattices (Parts 139 and 142) -/

noncomputable section

namespace SigabaNeo.Wall1

open Submodule Metric Set
open scoped RealInnerProductSpace Topology

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- Integer dual for the real inner product. -/
abbrev metricDual (L : Submodule ℤ V) := LinearMap.BilinForm.dualSubmodule (innerₗ V) L

/-- The projection has its intrinsic ambient space, so its dual is taken inside `S`. -/
def projectedModule (L : Submodule ℤ V) (S : Submodule ℝ V) : Submodule ℤ S :=
  L.map (S.orthogonalProjectionOnto.toLinearMap.restrictScalars ℤ)

/-- The dual of a projected module is the section of its dual. -/
theorem metricDual_projectedModule (L : Submodule ℤ V) (S : Submodule ℝ V) :
    metricDual (projectedModule L S) = (metricDual L).comap (S.subtype.restrictScalars ℤ) := by
  ext ξ
  change (∀ y ∈ projectedModule L S, ⟪ξ, y⟫ ∈ (1 : Submodule ℤ ℝ)) ↔
    ∀ x ∈ L, ⟪(ξ : V), x⟫ ∈ (1 : Submodule ℤ ℝ)
  constructor
  · intro h x hx
    rw [← S.inner_orthogonalProjectionOnto_eq_of_mem_left ξ x]
    exact h _ ⟨x, hx, rfl⟩
  · rintro h _ ⟨x, hx, rfl⟩
    exact (S.inner_orthogonalProjectionOnto_eq_of_mem_left ξ x).symm ▸ h x hx

theorem projectedModule_span_top (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L]
    (S : Submodule ℝ V) : span ℝ (projectedModule L S : Set S) = ⊤ := by
  change span ℝ (S.orthogonalProjectionOnto '' (L : Set V)) = ⊤
  rw [← LinearMap.coe_ofClass, ← Submodule.map_span, IsZLattice.span_top, Submodule.map_top]
  exact LinearMap.range_eq_top.mpr fun x ↦ ⟨x, S.orthogonalProjectionOnto_mem_subspace_eq_self x⟩

/-- Rounding parallel to a lattice vector gives a bounded lift of each projected point in
a bounded ball. This also works for a nonprimitive vector. -/
theorem projectedModule_discrete (L : Submodule ℤ V) [DiscreteTopology L] {v : V} (hv : v ∈ L) :
    DiscreteTopology (projectedModule L (ℝ ∙ v)ᗮ) := by
  let S := (ℝ ∙ v)ᗮ
  have : DiscreteTopology L.toAddSubgroup := ‹DiscreteTopology L›
  have hclosed : IsClosed (L : Set V) := L.toAddSubgroup.isClosed_of_discreteTopology
  apply discreteTopology_iff_isOpen_singleton.mpr
  intro y
  let R := ‖y‖ + 1
  let B := closedBall (0 : V) (R + ‖v‖)
  have hfin : (B ∩ (L : Set V)).Finite :=
    Metric.finite_isBounded_inter_isClosed DiscreteTopology.isDiscrete
      isBounded_closedBall hclosed
  apply isOpen_singleton_of_finite_mem_nhds y (ball_mem_nhds y zero_lt_one)
  apply ((hfin.image S.orthogonalProjectionOnto).preimage Subtype.val_injective.injOn).subset
  intro z hz
  obtain ⟨w, hw, he⟩ := z.property
  obtain ⟨k, hk, hlen⟩ := roundedLift_sq v w
  have he' : S.orthogonalProjectionOnto w = (z : S) := he
  have hn : ‖(ℝ ∙ v)ᗮ.starProjection w‖ = ‖z‖ := congrArg norm (congrArg Subtype.val he')
  have hz' : ‖z‖ < R := by
    have h := dist_triangle z y 0
    rw [dist_zero_right, dist_zero_right] at h
    change dist z y < 1 at hz
    change ‖z‖ < ‖y‖ + 1
    linarith
  refine ⟨w - k • v, ⟨?_, L.sub_mem hw (L.smul_mem _ hv)⟩, Subtype.ext (hk.trans
    (congrArg Subtype.val he'))⟩
  rw [mem_closedBall, dist_zero_right]
  rw [hn] at hlen
  have hR : 0 ≤ R := add_nonneg (norm_nonneg y) zero_le_one
  have hsq := (sq_le_sq₀ (norm_nonneg z) hR).2 hz'.le
  apply (sq_le_sq₀ (norm_nonneg _) (add_nonneg hR (norm_nonneg v))).1
  nlinarith [mul_nonneg hR (norm_nonneg v), sq_nonneg ‖v‖]

/-- Full-rank lattice projection along a lattice vector, in particular along a primitive one. -/
theorem projectedModule_isZLattice (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L]
    {v : V} (hv : v ∈ L) :
    letI := projectedModule_discrete L hv
    IsZLattice ℝ (projectedModule L (ℝ ∙ v)ᗮ) :=
  letI := projectedModule_discrete L hv
  ⟨projectedModule_span_top L _⟩

end SigabaNeo.Wall1

#print axioms SigabaNeo.Wall1.metricDual_projectedModule
#print axioms SigabaNeo.Wall1.projectedModule_discrete
#print axioms SigabaNeo.Wall1.projectedModule_isZLattice
