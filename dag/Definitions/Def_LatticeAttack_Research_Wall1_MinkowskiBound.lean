module

public import Mathlib.Algebra.Module.ZLattice.Covolume
public import Mathlib.MeasureTheory.Group.GeometryOfNumbers
public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit true

public section

open MeasureTheory Metric Module
namespace SigabaNeo.Wall1

variable {n : ℕ}

/-- The covolume of the integer span in orthonormal coordinates. -/
theorem minkowski_covolume_eq_abs_det (b : Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n))) :
    ZLattice.covolume (Submodule.span ℤ (Set.range b)) = |((EuclideanSpace.basisFun (Fin n) ℝ)).toBasis.det b| := by
  rw [ZLattice.covolume_eq_measure_fundamentalDomain _ volume
    (ZSpan.isAddFundamentalDomain b volume), ZSpan.measureReal_fundamentalDomain b volume ((EuclideanSpace.basisFun (Fin n) ℝ)).toBasis]
  simp [measureReal_def, measure_congr (ZSpan.fundamentalDomain_ae_parallelepiped ((EuclideanSpace.basisFun (Fin n) ℝ)).toBasis volume),
    ((EuclideanSpace.basisFun (Fin n) ℝ)).volume_parallelepiped]

/-- Minkowski's first-minimum bound at the critical closed-ball radius. -/
theorem minkowski_short_vector_det [NeZero n] (b : Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n))) :
    ∃ v ∈ Submodule.span ℤ (Set.range b), v ≠ 0 ∧
      ‖v‖ ^ n * volume.real (ball (0 : (EuclideanSpace ℝ (Fin n))) 1) ≤ 2 ^ n * |((EuclideanSpace.basisFun (Fin n) ℝ)).toBasis.det b| := by
  let V := volume.real (ball (0 : (EuclideanSpace ℝ (Fin n))) 1)
  let D := |((EuclideanSpace.basisFun (Fin n) ℝ)).toBasis.det b|
  have hV : 0 < V := ENNReal.toReal_pos (measure_ball_pos volume _ one_pos).ne'
    (measure_ball_lt_top.ne)
  let r := (2 ^ n * D / V) ^ (n : ℝ)⁻¹
  have hD : 0 ≤ D := abs_nonneg _
  have hr : 0 ≤ r := Real.rpow_nonneg (by positivity) _
  have hpow : r ^ n * V = 2 ^ n * D := by
    rw [show r ^ n = _ from Real.rpow_inv_natCast_pow (by positivity : 0 ≤ 2 ^ n * D / V)
      (NeZero.ne n), div_mul_cancel₀ _ hV.ne']
  have hF := ZLattice.covolume_eq_measure_fundamentalDomain _ volume
    (ZSpan.isAddFundamentalDomain b volume)
  rw [minkowski_covolume_eq_abs_det] at hF
  have hmeas : volume (ZSpan.fundamentalDomain b) * 2 ^ finrank ℝ (EuclideanSpace ℝ (Fin n)) ≤
      volume (closedBall (0 : (EuclideanSpace ℝ (Fin n))) r) := by
    apply (ENNReal.toReal_le_toReal (ENNReal.mul_ne_top
      (ZSpan.fundamentalDomain_isBounded b).measure_lt_top.ne (by finiteness))
      (isCompact_closedBall _ _).measure_lt_top.ne).mp
    rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ← measureReal_def, ← measureReal_def,
      ← hF, volume.addHaar_real_closedBall _ hr, finrank_euclideanSpace_fin]
    simpa [mul_comm] using hpow.ge
  let : Countable (Submodule.span ℤ (Set.range b)).toAddSubgroup :=
    inferInstanceAs (Countable (Submodule.span ℤ (Set.range b)))
  let : DiscreteTopology (Submodule.span ℤ (Set.range b)).toAddSubgroup :=
    inferInstanceAs (DiscreteTopology (Submodule.span ℤ (Set.range b)))
  obtain ⟨x, hx, hxr⟩ := exists_ne_zero_mem_lattice_of_measure_mul_two_pow_le_measure
    (ZSpan.isAddFundamentalDomain' b volume)
    (fun x hx ↦ by simpa [mem_closedBall_zero_iff] using hx)
    (convex_closedBall (0 : (EuclideanSpace ℝ (Fin n))) r) (isCompact_closedBall _ _) hmeas
  refine ⟨x, x.property, fun h ↦ hx (Subtype.ext h), ?_⟩
  exact (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _)
    (mem_closedBall_zero_iff.mp hxr) n) hV.le).trans_eq hpow

/-- Intrinsic Gram-determinant form of Minkowski's first-minimum bound. -/
theorem minkowski_short_vector_gram [NeZero n] (b : Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n))) :
    ∃ v ∈ Submodule.span ℤ (Set.range b), v ≠ 0 ∧
      ‖v‖ ^ n * volume.real (ball (0 : (EuclideanSpace ℝ (Fin n))) 1) ≤ 2 ^ n * Real.sqrt (Matrix.gram ℝ b).det := by
  rw [Matrix.gram_eq_conjTranspose_mul (EuclideanSpace.basisFun (Fin n) ℝ) b, Matrix.det_mul, Matrix.det_conjTranspose]
  have hm : ((EuclideanSpace.basisFun (Fin n) ℝ)).toBasis.toMatrix b = Matrix.of (fun i j ↦ ((EuclideanSpace.basisFun (Fin n) ℝ)).repr (b j) i) := by
    ext i j
    exact ((EuclideanSpace.basisFun (Fin n) ℝ)).coe_toBasis_repr_apply _ _
  simpa [← sq, Real.sqrt_sq_eq_abs, Basis.det_apply, hm] using minkowski_short_vector_det b

#print axioms minkowski_covolume_eq_abs_det
#print axioms minkowski_short_vector_det
#print axioms minkowski_short_vector_gram

end SigabaNeo.Wall1
