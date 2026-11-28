import Definitions.Def_LatticeAttack_Research_Wall1_AppendDual
import Definitions.Def_LatticeAttack_Research_Wall1_MarkedIntegerSection
import Mathlib.Analysis.Normed.Group.AddCircle

set_option autoImplicit true

/-! # Character transport through an arbitrary append and projection -/

noncomputable section

namespace SigabaNeo.Wall1

open Submodule WithLp
open scoped RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
variable {ι : Type*} (L : Submodule ℤ V) (u : V) (v : WindowSpace V)

abbrev dualParent (x : metricDual (retainedWindow L u v)) : metricDual L :=
  ⟨x.val.val.fst, ((mem_metricDual_retainedWindow L u v x.val).1 x.property).1⟩

/-- The vertical displacement modulo one, for every choice of projected direction. -/
theorem retained_kick (x : metricDual (retainedWindow L u v)) :
    (x.val.val.snd : UnitAddCircle) = -(⟪(dualParent L u v x : V), u⟫ : UnitAddCircle) := by
  obtain ⟨j, hj⟩ := Submodule.mem_one.mp
    (((mem_metricDual_retainedWindow L u v x.val).1 x.property).2)
  apply eq_neg_of_add_eq_zero_left
  rw [add_comm, ← AddCircle.coe_add, AddCircle.coe_eq_zero_iff]
  exact ⟨j, by simpa using hj⟩

theorem retained_kick_norm (x : metricDual (retainedWindow L u v)) :
    ‖(dualParent L u v x : V)‖ ^ 2 + ‖(⟪(dualParent L u v x : V), u⟫ : UnitAddCircle)‖ ^ 2
      ≤ ‖x.val‖ ^ 2 := by
  have he := congrArg norm (retained_kick L u v x)
  rw [norm_neg] at he
  have hle : ‖(x.val.val.snd : UnitAddCircle)‖ ≤ ‖x.val.val.snd‖ :=
    QuotientAddGroup.norm_mk_le_norm
  change _ ≤ ‖x.val.val‖ ^ 2
  rw [WithLp.prod_norm_sq_eq_of_L2, ← he]
  exact add_le_add le_rfl (pow_le_pow_left₀ (norm_nonneg _) hle 2)

/-- The projected old horizontal generators of the new mark. -/
abbrev nextMark (g : ι → V) (i : ι) : (ℝ ∙ v)ᗮ :=
  (ℝ ∙ v)ᗮ.orthogonalProjectionOnto (horizontalInclusion (g i))

theorem nextMark_multiple (g : ι → V) (q : ℕ) (hq : ∀ i, q • g i ∈ L) (i : ι) :
    q • nextMark v g i ∈ retainedWindow L u v := by
  refine ⟨horizontalInclusion (q • g i), mem_sup_left ⟨_, hq i, rfl⟩, ?_⟩
  simp [nextMark, map_nsmul]

/-- Pairings with old horizontal representatives agree even before reduction modulo one. -/
theorem retained_pairing_transport (x : metricDual (retainedWindow L u v)) (y : V) :
    ⟪x.val, (ℝ ∙ v)ᗮ.orthogonalProjectionOnto (horizontalInclusion y)⟫ =
      ⟪(dualParent L u v x : V), y⟫ := by
  rw [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left]
  change ⟪x.val.val.fst, y⟫ + (0 : ℝ) * x.val.val.snd = ⟪x.val.val.fst, y⟫
  simp

theorem retained_label_transport (g : ι → V) (q : ℕ) (hq : ∀ i, q • g i ∈ L)
    (x : metricDual (retainedWindow L u v)) :
    markLabel _ (nextMark v g) q (nextMark_multiple L u v g q hq) x =
      markLabel L g q hq (dualParent L u v x) := by
  funext i
  obtain ⟨a, ha, hea⟩ := markLabel_apply_spec _ _ _ _ x i
  obtain ⟨b, hb, heb⟩ := markLabel_apply_spec _ _ _ _ (dualParent L u v x) i
  rw [hea, heb]
  congr 1
  apply Int.cast_injective (α := ℝ)
  rw [ha, hb, nextMark, retained_pairing_transport]

omit [FiniteDimensional ℝ V] in
theorem markLabel_character (g : ι → V) (q : ℕ) [NeZero q] (hq : ∀ i, q • g i ∈ L)
    (x : metricDual L) (i : ι) :
    ZMod.toAddCircle (markLabel L g q hq x i) = (⟪(x : V), g i⟫ : UnitAddCircle) := by
  obtain ⟨z, hz, he⟩ := markLabel_apply_spec _ _ _ _ x i
  rw [he, ZMod.toAddCircle_intCast, hz, mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr (NeZero.ne q))]

/-- An arbitrary lift of a marked column has the same kick, given by the residue dot product
divided by the modulus in the additive circle. -/
theorem retained_label_kick [Fintype ι] (g : ι → V) (q : ℕ) [NeZero q]
    (hq : ∀ i, q • g i ∈ L) (a : ι → ℤ) (hu : u - ∑ i, a i • g i ∈ L)
    (x : metricDual (retainedWindow L u v)) :
    (x.val.val.snd : UnitAddCircle) =
      -ZMod.toAddCircle (∑ i, a i • markLabel L g q hq (dualParent L u v x) i) := by
  let p := dualParent L u v x
  rw [retained_kick]
  congr 1
  simp only [map_sum, map_zsmul, markLabel_character]
  have hi := p.property _ hu
  obtain ⟨j, hj⟩ := Submodule.mem_one.mp hi
  change (j : ℝ) = ⟪(p : V), u - ∑ i, a i • g i⟫ at hj
  rw [inner_sub_right, inner_sum] at hj
  simp only [← Int.cast_smul_eq_zsmul ℝ, real_inner_smul_right] at hj
  have hzero : ((⟪(p : V), u⟫ - ∑ i, (a i : ℝ) * ⟪(p : V), g i⟫ : ℝ) : UnitAddCircle) = 0 :=
    (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr ⟨j, by simpa using hj⟩
  rw [AddCircle.coe_sub, sub_eq_zero] at hzero
  change (⟪(p : V), u⟫ : UnitAddCircle) = _
  rw [hzero]
  change QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ)) _ = _
  simp only [map_sum, ← zsmul_eq_mul, map_zsmul]
  rfl

end SigabaNeo.Wall1

#print axioms SigabaNeo.Wall1.retained_kick
#print axioms SigabaNeo.Wall1.retained_kick_norm
#print axioms SigabaNeo.Wall1.retained_pairing_transport
#print axioms SigabaNeo.Wall1.retained_label_transport
#print axioms SigabaNeo.Wall1.markLabel_character
#print axioms SigabaNeo.Wall1.retained_label_kick
