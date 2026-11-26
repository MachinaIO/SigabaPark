import Definitions.Def_LatticeAttack_Research_Wall1_ProjectionDual
import CslibFrontier.Foundations.Analysis.Lattice.Minimum

set_option autoImplicit true

/-! # The dual minimum after a unit-height append and orthogonal projection -/

noncomputable section

namespace SigabaNeo.Wall1

open Submodule WithLp ZLattice
open scoped RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

abbrev WindowSpace (V : Type*) := WithLp 2 (V × ℝ)

/-- Horizontal inclusion in the orthogonal product. -/
def horizontalInclusion : V →ₗ[ℝ] WindowSpace V :=
  (WithLp.linearEquiv 2 ℝ (V × ℝ)).symm.toLinearMap.comp (LinearMap.inl ℝ V ℝ)

/-- Append the generator with displacement `u` and vertical height one. -/
def appendWindow (L : Submodule ℤ V) (u : V) : Submodule ℤ (WindowSpace V) :=
  L.map (horizontalInclusion.restrictScalars ℤ) ⊔ ℤ ∙ toLp 2 (u, (1 : ℝ))

/-- Lattice retained upon selecting `v` in the appended window. -/
def retainedWindow (L : Submodule ℤ V) (u : V) (v : WindowSpace V) :=
  projectedModule (appendWindow L u) (ℝ ∙ v)ᗮ

omit [FiniteDimensional ℝ V] in
/-- Pairing integrally with the window is equivalent to the old dual condition and one
integrality condition on the vertical coordinate. -/
theorem mem_metricDual_appendWindow (L : Submodule ℤ V) (u : V) (ξ : WindowSpace V) :
    ξ ∈ metricDual (appendWindow L u) ↔
      ξ.fst ∈ metricDual L ∧ ⟪ξ.fst, u⟫ + ξ.snd ∈ (1 : Submodule ℤ ℝ) := by
  let T := (1 : Submodule ℤ ℝ).comap (((innerₗ (WindowSpace V)) ξ).restrictScalars ℤ)
  change appendWindow L u ≤ T ↔ _
  rw [appendWindow, sup_le_iff, Submodule.map_le_iff_le_comap, Submodule.span_singleton_le_iff_mem]
  constructor <;> rintro ⟨h, h'⟩
  · refine ⟨fun x hx ↦ ?_, ?_⟩
    · have hx' := h hx
      change ⟪ξ.fst, x⟫ + (0 : ℝ) * ξ.snd ∈ (1 : Submodule ℤ ℝ) at hx'
      simpa using hx'
    · change ⟪ξ.fst, u⟫ + 1 * ξ.snd ∈ (1 : Submodule ℤ ℝ) at h'
      simpa using h'
  · constructor
    · intro x hx
      change ⟪ξ.fst, x⟫ + (0 : ℝ) * ξ.snd ∈ (1 : Submodule ℤ ℝ)
      simpa using h x hx
    · change ⟪ξ.fst, u⟫ + 1 * ξ.snd ∈ (1 : Submodule ℤ ℝ)
      simpa using h'

theorem mem_metricDual_retainedWindow (L : Submodule ℤ V) (u : V) (v : WindowSpace V)
    (ξ : (ℝ ∙ v)ᗮ) :
    ξ ∈ metricDual (retainedWindow L u v) ↔
      ξ.val.fst ∈ metricDual L ∧ ⟪ξ.val.fst, u⟫ + ξ.val.snd ∈ (1 : Submodule ℤ ℝ) := by
  rw [retainedWindow, metricDual_projectedModule]
  exact mem_metricDual_appendWindow L u ξ.val

omit [FiniteDimensional ℝ V] in
private theorem snd_ne_zero_of_fst_zero {v : WindowSpace V} (ξ : (ℝ ∙ v)ᗮ)
    (hξ : ξ ≠ 0) (hf : ξ.val.fst = 0) : ξ.val.snd ≠ 0 := by
  intro hs
  apply hξ
  apply Subtype.ext
  exact (WithLp.equiv 2 (V × ℝ)).injective (Prod.ext hf hs)

/-- The lower bound holds for every selected direction, regardless of the tie rule.
The nonzero-dual hypothesis accounts for `ZLattice.minimum ⊥ = 0`. -/
theorem retained_dual_minimum (L : Submodule ℤ V) (u : V) (v : WindowSpace V)
    (hD : metricDual (retainedWindow L u v) ≠ ⊥) :
    min (minimum (metricDual L)) 1 ≤ minimum (metricDual (retainedWindow L u v)) := by
  apply (le_minimum_iff hD).2
  intro ξ hξ h0
  obtain ⟨hd, hj⟩ := (mem_metricDual_retainedWindow L u v ξ).mp hξ
  by_cases hf : ξ.val.fst = 0
  · rw [hf, inner_zero_left, zero_add, Submodule.mem_one] at hj
    obtain ⟨j, hj⟩ := hj
    have hne := snd_ne_zero_of_fst_zero ξ h0 hf
    have hj0 : j ≠ 0 := by rintro rfl; exact hne (by simpa using hj.symm)
    have hle : (1 : ℝ) ≤ |(j : ℝ)| := by exact_mod_cast Int.one_le_abs hj0
    apply (min_le_right _ _).trans
    exact (by simpa [← hj, Real.norm_eq_abs] using hle : (1 : ℝ) ≤ ‖ξ.val.snd‖).trans
      (WithLp.norm_snd_le V ξ.val)
  · exact (min_le_left _ _).trans ((minimum_le_norm hd hf).trans (WithLp.norm_fst_le V ξ.val))

/-- A nonhorizontal winner rules out a purely vertical nonzero dual vector. -/
theorem retained_dual_minimum_of_vertical (L : Submodule ℤ V) (u : V) (v : WindowSpace V)
    (hv : v.snd ≠ 0) (hD : metricDual (retainedWindow L u v) ≠ ⊥) :
    minimum (metricDual L) ≤ minimum (metricDual (retainedWindow L u v)) := by
  apply (le_minimum_iff hD).2
  intro ξ hξ h0
  have hf : ξ.val.fst ≠ 0 := by
    intro hf
    have ho := mem_orthogonal_singleton_iff_inner_left.mp ξ.property
    change ⟪ξ.val.fst, v.fst⟫ + v.snd * ξ.val.snd = 0 at ho
    rw [hf, inner_zero_left, zero_add] at ho
    exact (mul_ne_zero hv (snd_ne_zero_of_fst_zero ξ h0 hf)) ho
  exact (minimum_le_norm ((mem_metricDual_retainedWindow L u v ξ).mp hξ).1 hf).trans
    (WithLp.norm_fst_le V ξ.val)

section FullRank

open Module

private theorem appendWindow_basis_span (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L]
    (u : V) : ∃ b : Basis (Unit ⊕ Free.ChooseBasisIndex ℤ L) ℝ (WindowSpace V),
      appendWindow L u = span ℤ (Set.range b) := by
  let c := (Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L
  let shear := (LinearEquiv.refl ℝ ℝ).skewProd (LinearEquiv.refl ℝ V)
    (LinearMap.toSpanSingleton ℝ V u)
  let e := shear.trans ((LinearEquiv.prodComm ℝ ℝ V).trans (WithLp.linearEquiv 2 ℝ (V × ℝ)).symm)
  let b := ((Basis.singleton Unit ℝ).prod c).map e
  refine ⟨b, ?_⟩
  have hb : ⇑b = Sum.elim (fun _ : Unit ↦ toLp 2 (u, (1 : ℝ)))
      (fun i ↦ horizontalInclusion (c i)) := by
    funext i
    cases i with
    | inl i =>
      simp [b, e, shear, Basis.prod_apply, LinearEquiv.skewProd_apply]
    | inr i =>
      simp [b, e, shear, Basis.prod_apply, LinearEquiv.skewProd_apply, horizontalInclusion]
  rw [hb, Set.Sum.elim_range, Submodule.span_union, Set.range_const, sup_comm, appendWindow]
  congr 1
  conv_lhs => rw [← (Free.chooseBasis ℤ L).ofZLatticeBasis_span ℝ, Submodule.map_span]
  rw [← Set.range_comp]
  rfl

/-- A unit-height append to a full lattice is a full lattice in the enlarged space. -/
theorem appendWindow_lattice (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L] (u : V) :
    ∃ _ : DiscreteTopology (appendWindow L u), IsZLattice ℝ (appendWindow L u) := by
  obtain ⟨b, hb⟩ := appendWindow_basis_span L u
  rw [hb]
  exact ⟨inferInstance, inferInstance⟩

/-- A full-rank positive-dimensional retained state needs no separate nonzero-dual hypothesis. -/
theorem lattice_retained_dual_minimum (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L]
    [Nontrivial V] (u : V) {v : WindowSpace V} (hv : v ∈ appendWindow L u) (hv0 : v ≠ 0) :
    min (minimum (metricDual L)) 1 ≤ minimum (metricDual (retainedWindow L u v)) ∧
    (v.snd ≠ 0 → minimum (metricDual L) ≤ minimum (metricDual (retainedWindow L u v))) := by
  obtain ⟨hW, hW'⟩ := appendWindow_lattice L u
  have : DiscreteTopology (retainedWindow L u v) := projectedModule_discrete _ hv
  have : IsZLattice ℝ (retainedWindow L u v) := projectedModule_isZLattice _ hv
  let D := metricDual (retainedWindow L u v)
  have : DiscreteTopology D := discreteTopology_dualSubmodule _
  have : IsZLattice ℝ D := isZLattice_dualSubmodule _
  have hdim := (ℝ ∙ v).finrank_add_finrank_orthogonal
  rw [finrank_span_singleton hv0, (WithLp.linearEquiv 2 ℝ (V × ℝ)).finrank_eq,
    Module.finrank_prod, Module.finrank_self] at hdim
  have hrank := ZLattice.rank ℝ D
  have hpos : 0 < finrank ℝ V := finrank_pos
  have hnt : Nontrivial D := nontrivial_of_finrank_pos (R := ℤ) (by omega)
  have hD := (Submodule.nontrivial_iff_ne_bot (p := D)).mp hnt
  exact ⟨retained_dual_minimum L u v hD, fun h ↦ retained_dual_minimum_of_vertical L u v h hD⟩

end FullRank
end SigabaNeo.Wall1

#print axioms SigabaNeo.Wall1.mem_metricDual_appendWindow
#print axioms SigabaNeo.Wall1.mem_metricDual_retainedWindow
#print axioms SigabaNeo.Wall1.retained_dual_minimum
#print axioms SigabaNeo.Wall1.retained_dual_minimum_of_vertical
#print axioms SigabaNeo.Wall1.appendWindow_lattice
#print axioms SigabaNeo.Wall1.lattice_retained_dual_minimum
