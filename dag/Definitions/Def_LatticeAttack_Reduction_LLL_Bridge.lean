module

public import Definitions.Def_LatticeAttack_Reduction_LLL_Algorithm
public import Definitions.Def_LatticeAttack_Reduction_LLL_Reduced
import all Definitions.Def_LatticeAttack_Reduction_LLL_Reduced

set_option autoImplicit true

@[expose] public section

namespace SigabaNeo.LLL.Algorithm

open InnerProductSpace
open scoped RealInnerProductSpace

variable {n d : ℕ}

noncomputable def realVec (x : Fin d → ℚ) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 fun a ↦ (x a : ℝ)

noncomputable def realRows (B : Rows n d) (i : Fin n) := realVec (rationalRow B i)

private theorem dot_cast (x y : Fin d → ℚ) :
    (dot x y : ℝ) = ⟪realVec y, realVec x⟫_ℝ := by
  simp [dot, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, realVec]

private theorem norm_cast (x : Fin d → ℚ) :
    (dot x x : ℝ) = ‖realVec x‖ ^ 2 := by rw [dot_cast, real_inner_self_eq_norm_sq]

theorem starRow_cast (B : Rows n d) (i : Fin n) :
    realVec (starRow B i) = gramSchmidt ℝ (realRows B) i := by
  classical
  rw [starRow, gramSchmidt_def]
  ext a
  simp only [realVec, WithLp.ofLp_toLp, Pi.sub_apply, Rat.cast_sub,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Rat.cast_sum, Rat.cast_mul, Rat.cast_div,
    PiLp.sub_apply, WithLp.ofLp_sum, Submodule.starProjection_singleton, WithLp.ofLp_smul]
  congr 1
  apply Finset.sum_bij (fun (j : Fin i.val) _ ↦ (⟨j.val, lt_trans j.isLt i.isLt⟩ : Fin n))
  · exact fun j _ ↦ Finset.mem_Iio.mpr j.isLt
  · exact fun _ _ _ _ h ↦ Fin.ext (congrArg (@Fin.val n) h)
  · exact fun j hj ↦ ⟨⟨j.val, show j < i from Finset.mem_Iio.mp hj⟩, Finset.mem_univ _, rfl⟩
  · intro j _
    let k : Fin n := ⟨j.val, lt_trans j.isLt i.isLt⟩
    have ih := starRow_cast B k
    rw [dot_cast, norm_cast]
    simp [← ih, realRows, k, realVec, WithLp.ofLp_toLp]
termination_by i.val
decreasing_by exact j.isLt

theorem reduced_cast (B : Rows n n) (hr : Reduced B) : LLLReduced (realRows B) := by
  have hn (i : Fin n) : (normSq B i : ℝ) = ‖gramSchmidt ℝ (realRows B) i‖ ^ 2 := by
    rw [normSq, norm_cast, starRow_cast]
  have hm (i j : Fin n) : (mu B i j : ℝ) = LLL.mu (realRows B) i j := by
    rw [mu, Rat.cast_div, dot_cast, hn, starRow_cast]
    rfl
  constructor
  · intro i j hij
    rw [← hm]
    simpa using (Rat.cast_le (K := ℝ)).mpr (hr.1 i j hij)
  · intro i j hij
    have h := hr.2 j i hij.symm
    unfold lovasz at h
    have h' : (3 / 4 : ℝ) * (normSq B i : ℝ) ≤
        (normSq B j : ℝ) + (mu B j i : ℝ) ^ 2 * (normSq B i : ℝ) := by
      simpa using (Rat.cast_le (K := ℝ)).mpr h
    rw [hn, hn, hm] at h'
    linarith

private noncomputable def embedInt : (Fin d → ℤ) →ₗ[ℤ] EuclideanSpace ℝ (Fin d) where
  toFun x := WithLp.toLp 2 fun a ↦ (x a : ℝ)
  map_add' x y := by ext; simp
  map_smul' z x := by ext; simp

theorem run_real_span (fuel : ℕ) (B : Rows n d) :
    Submodule.span ℤ (Set.range (realRows (run fuel B).rows)) =
      Submodule.span ℤ (Set.range (realRows B)) := by
  have h := congrArg (Submodule.map (embedInt (d := d))) (run_lattice fuel B)
  unfold realRows
  simpa [lattice, Submodule.map_span, ← Set.range_comp, Function.comp_def, realRows,
    realVec, rationalRow, embedInt] using h

theorem run_approx_of_normal [NeZero n] (fuel : ℕ) (B : Rows n n)
    (hb : LinearIndependent ℝ (realRows B)) (hn : (run fuel B).normal = true)
    (v : EuclideanSpace ℝ (Fin n)) (hv : v ∈ Submodule.span ℤ (Set.range (realRows B)))
    (hne : v ≠ 0) :
    ‖realRows (run fuel B).rows 0‖ ≤ (2 : ℝ) ^ (((n : ℝ) - 1) / 2) * ‖v‖ := by
  have hs := run_real_span fuel B
  apply reduced_approx_factor _ _ (reduced_cast _ (run_reduced fuel B hn)) v (hs.ge hv) hne
  apply linearIndependent_of_top_le_span_of_card_eq_finrank _ (by simp)
  rw [← Submodule.span_span_of_tower ℤ ℝ, hs, Submodule.span_span_of_tower,
    hb.span_eq_top_of_card_eq_finrank' (by simp)]

#print axioms run_approx_of_normal
#print axioms starRow_cast
#print axioms reduced_cast
#print axioms run_real_span

end SigabaNeo.LLL.Algorithm
