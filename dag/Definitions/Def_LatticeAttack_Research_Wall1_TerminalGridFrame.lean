import Definitions.Def_LatticeAttack_Research_Wall1_BlichfeldtTerminal506
import Definitions.Def_LatticeAttack_Research_Wall1_TerminalCountObstruction
import Definitions.Def_LatticeAttack_Research_Wall1_ProjectedCovolume

set_option autoImplicit true

/-! # Projected coordinate axes along a unit-height chain

A Parseval frame records the projections of all the raw coordinate axes. Appending adds a
unit axis; freezing projects each frame vector. The analysis map recovers an isometric
realization inside the original coordinate space, with equality of integer modules.
-/

noncomputable section
namespace SigabaNeo.Wall1.TerminalProjection

open Module Submodule WithLp MeasureTheory DecoupledDecoder
open scoped RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
variable {n : ℕ}

/-- Inner products against the projected axes recover physical squared length. -/
structure AxisFrame (n : ℕ) (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] where
  axis : Fin n → V
  parseval : ∀ x, ∑ i, ⟪axis i, x⟫ ^ 2 = ‖x‖ ^ 2

namespace AxisFrame

def ofBasis (b : OrthonormalBasis (Fin n) ℝ V) : AxisFrame n V :=
  ⟨b, b.sum_sq_inner_right⟩

def project (f : AxisFrame n V) (S : Submodule ℝ V) : AxisFrame n S where
  axis i := S.orthogonalProjectionOnto (f.axis i)
  parseval x := by
    simp only [inner_orthogonalProjectionOnto_eq_of_mem_right]
    exact f.parseval x.val

def append (f : AxisFrame n V) : AxisFrame (n + 1) (WindowSpace V) where
  axis := Fin.snoc (fun i ↦ horizontalInclusion (f.axis i)) (toLp 2 (0, 1))
  parseval x := by
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
    change (∑ i, (⟪f.axis i, x.fst⟫ + x.snd * 0)^2) +
      (⟪(0 : V), x.fst⟫ + x.snd * 1)^2 = _
    simp [f.parseval, WithLp.prod_norm_sq_eq_of_L2, Real.norm_eq_abs]

abbrev integerSpan (f : AxisFrame n V) := span ℤ (Set.range f.axis)

theorem integerSpan_project (f : AxisFrame n V) (S : Submodule ℝ V) :
    (f.project S).integerSpan = projectedModule f.integerSpan S := by
  rw [projectedModule, integerSpan, map_span, ← Set.range_comp]
  rfl

omit [FiniteDimensional ℝ V] in
theorem integerSpan_append (f : AxisFrame n V) :
    f.append.integerSpan = appendWindow f.integerSpan 0 := by
  rw [integerSpan, appendWindow, integerSpan, map_span, ← Set.range_comp, ← span_union]
  simp [append, Set.union_singleton, Function.comp_def]

def analysisMap (f : AxisFrame n V) : V →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n) where
  toFun x := toLp 2 (fun i ↦ ⟪f.axis i, x⟫)
  map_add' x y := by ext i; exact inner_add_right _ _ _
  map_smul' c x := by ext i; exact real_inner_smul_right _ _ _
  norm_map' x := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [EuclideanSpace.real_norm_sq_eq]
    exact f.parseval x

abbrev space (f : AxisFrame n V) := f.analysisMap.toLinearMap.range
abbrev embed (f : AxisFrame n V) := f.analysisMap.equivRange

local notation "axes" => EuclideanSpace.basisFun (Fin n) ℝ

theorem project_axis (f : AxisFrame n V) (i : Fin n) :
    f.space.orthogonalProjectionOnto (axes i) = f.embed (f.axis i) := by
  apply ext_inner_left ℝ
  intro y
  obtain ⟨x, rfl⟩ := f.embed.surjective y
  rw [inner_orthogonalProjectionOnto_eq_of_mem_left, LinearIsometryEquiv.inner_map_map]
  change ⟪f.analysisMap x, axes i⟫ = _
  rw [real_inner_comm, EuclideanSpace.basisFun_inner]
  exact real_inner_comm _ _

theorem grid_eq (f : AxisFrame n V) :
    projectedModule (span ℤ (Set.range axes)) f.space =
      f.integerSpan.map (f.embed.toLinearEquiv.toLinearMap.restrictScalars ℤ) := by
  simp only [projectedModule, integerSpan, map_span, ← Set.range_comp]
  congr 2
  funext i
  exact f.project_axis i

end AxisFrame
end SigabaNeo.Wall1.TerminalProjection

#print axioms SigabaNeo.Wall1.TerminalProjection.AxisFrame.grid_eq
#print axioms SigabaNeo.Wall1.TerminalProjection.AxisFrame.integerSpan_append
#print axioms SigabaNeo.Wall1.TerminalProjection.AxisFrame.integerSpan_project
