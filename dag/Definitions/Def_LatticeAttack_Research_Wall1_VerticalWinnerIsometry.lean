import Definitions.Def_LatticeAttack_Research_Wall1_AppendDual

set_option autoImplicit true

/-! # The vertical-winner isometry (Part 139, Theorem 4(a)) -/

noncomputable section

namespace SigabaNeo.Wall1

open Submodule WithLp
open scoped RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

private def negativePole (v : WindowSpace V) : WindowSpace V := toLp 2 (0, -‖v‖)

/-- Reflect the winner to the negative vertical axis. -/
def winnerStraightening (v : WindowSpace V) : WindowSpace V ≃ₗᵢ[ℝ] WindowSpace V :=
  (ℝ ∙ (v - negativePole v))ᗮ.reflection

omit [FiniteDimensional ℝ V] in
private theorem straighten_winner (v : WindowSpace V) :
    winnerStraightening v v = negativePole v := by
  apply reflection_sub
  simp [negativePole, WithLp.norm_toLp_snd]

/-- The rank-one compression, written without a division by the horizontal length.
For positive vertical height it also covers a purely vertical winner. -/
def winnerCompression (v : WindowSpace V) : V →ₗ[ℝ] V :=
  LinearMap.id - (‖v‖ * (‖v‖ + v.snd))⁻¹ •
    (InnerProductSpace.rankOne ℝ v.fst v.fst).toLinearMap

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] in
private theorem horizontal_norm_identity (v : WindowSpace V) :
    ‖v - negativePole v‖ ^ 2 = 2 * ‖v‖ * (‖v‖ + v.snd) := by
  have hv := WithLp.prod_norm_sq_eq_of_L2 v
  rw [WithLp.prod_norm_sq_eq_of_L2]
  simp only [negativePole, sub_fst, toLp_fst, sub_zero, sub_snd, toLp_snd, Real.norm_eq_abs,
    sq_abs] at *
  nlinarith

omit [FiniteDimensional ℝ V] in
/-- The isometry sends the projected horizontal vector exactly to the compressed one. -/
theorem straighten_project_horizontal (v : WindowSpace V) (hk : 0 < v.snd) (x : V) :
    winnerStraightening v ((ℝ ∙ v)ᗮ.starProjection (horizontalInclusion x)) =
      horizontalInclusion (winnerCompression v x) := by
  let R := winnerStraightening v
  let n := v - negativePole v
  let w := (ℝ ∙ v)ᗮ.starProjection (horizontalInclusion x)
  have hs : 0 < ‖v‖ := by
    apply norm_pos_iff.mpr
    rintro rfl
    exact (lt_irrefl 0) hk
  have hsum := add_pos hs hk
  have ha : (R w).snd = 0 := by
    have ho := mem_orthogonal_singleton_iff_inner_left.mp
      ((ℝ ∙ v)ᗮ.starProjection_apply_mem (horizontalInclusion x))
    have h := R.inner_map_map w v
    change ⟪R w, winnerStraightening v v⟫ = ⟪w, v⟫ at h
    rw [straighten_winner, show ⟪w, v⟫ = 0 from ho] at h
    change ⟪(R w).fst, (0 : V)⟫ + (-‖v‖) * (R w).snd = 0 at h
    simpa [hs.ne', inner_zero_right] using h
  have hf : (R w).fst = (R (horizontalInclusion x)).fst := by
    dsimp only [w]
    rw [starProjection_orthogonal_val, starProjection_singleton, map_sub, map_smul,
      sub_fst, smul_fst, show R v = negativePole v from straighten_winner v]
    simp [negativePole]
  have hn : ⟪n, horizontalInclusion x⟫ = ⟪v.fst, x⟫ := by
    change ⟪v.fst - 0, x⟫ + 0 * (v.snd - -‖v‖) = _
    simp
  apply (WithLp.equiv 2 (V × ℝ)).injective
  apply Prod.ext
  · change (R w).fst = winnerCompression v x
    rw [hf]
    change ((ℝ ∙ n)ᗮ.reflection (horizontalInclusion x)).fst = _
    rw [reflection_orthogonal_apply, reflection_singleton_apply, neg_fst, sub_fst, smul_fst,
      smul_fst, hn]
    change -(2 • ((⟪v.fst, x⟫ / ‖n‖ ^ 2) • (v.fst - 0)) - x) =
      x - (‖v‖ * (‖v‖ + v.snd))⁻¹ • (⟪v.fst, x⟫ • v.fst)
    rw [sub_zero, neg_sub, two_smul, ← add_smul, smul_smul]
    congr 2
    rw [show ‖n‖ ^ 2 = _ from horizontal_norm_identity v]
    field_simp
    ring
  · exact ha

omit [FiniteDimensional ℝ V] in
/-- The exact squared-length formula for the compression. -/
theorem winnerCompression_norm_sq (v : WindowSpace V) (hk : 0 < v.snd) (x : V) :
    ‖winnerCompression v x‖ ^ 2 = ‖x‖ ^ 2 - ⟪v.fst, x⟫ ^ 2 / ‖v‖ ^ 2 := by
  have hh (y : V) : ‖horizontalInclusion y‖ = ‖y‖ := WithLp.norm_toLp_fst 2 V ℝ y
  have hs : 0 < ‖v‖ := norm_pos_iff.mpr (by rintro rfl; exact (lt_irrefl 0) hk)
  have he := congrArg norm (straighten_project_horizontal v hk x)
  rw [LinearIsometryEquiv.norm_map, hh] at he
  have hp := norm_sq_eq_add_norm_sq_starProjection (horizontalInclusion x) (ℝ ∙ v)
  rw [he, hh, starProjection_singleton, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] at hp
  have hi : ⟪v, horizontalInclusion x⟫ = ⟪v.fst, x⟫ := by
    change ⟪v.fst, x⟫ + 0 * v.snd = _
    simp
  rw [hi] at hp
  change ‖x‖ ^ 2 = (⟪v.fst, x⟫ / ‖v‖ ^ 2) ^ 2 * ‖v‖ ^ 2 + ‖winnerCompression v x‖ ^ 2 at hp
  have hterm : (⟪v.fst, x⟫ / ‖v‖ ^ 2) ^ 2 * ‖v‖ ^ 2 = ⟪v.fst, x⟫ ^ 2 / ‖v‖ ^ 2 := by
    field_simp [hs.ne']
  linarith only [hp, hterm]

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] in
private theorem zspan_neg_singleton (x : WindowSpace V) : ℤ ∙ -x = ℤ ∙ x := by
  apply le_antisymm <;> rw [span_singleton_le_iff_mem]
  · exact (ℤ ∙ x).neg_mem (mem_span_singleton_self x)
  · simpa using (ℤ ∙ -x).neg_mem (mem_span_singleton_self (-x))

/-- Under the ambient linear isometry, the entire retained lattice is the horizontal copy
of the compressed refinement. The theorem applies to any such lattice vector, including
every primitive shortest winner with positive integer vertical index. -/
theorem verticalWinner_isometry (L : Submodule ℤ V) (u l : V)
    (k : ℕ) (hk : 0 < k) (v : WindowSpace V)
    (hv : v = horizontalInclusion l + (k : ℝ) • toLp 2 (u, (1 : ℝ))) :
    (retainedWindow L u v).map
        (((winnerStraightening v).toLinearMap.comp (ℝ ∙ v)ᗮ.subtype).restrictScalars ℤ) =
      (L ⊔ ℤ ∙ ((k : ℝ)⁻¹ • l)).map
        ((horizontalInclusion.comp (winnerCompression v)).restrictScalars ℤ) := by
  let R := winnerStraightening v
  let F := R.toLinearMap.comp (ℝ ∙ v)ᗮ.starProjection.toLinearMap
  let G := horizontalInclusion.comp (winnerCompression v)
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hvs : v.snd = (k : ℝ) := by rw [hv]; change 0 + (k : ℝ) * 1 = _; ring
  have hhor (x : V) : F (horizontalInclusion x) = G x :=
    straighten_project_horizontal v (hvs ▸ hkR) x
  have hkill : F v = 0 := by
    change R ((ℝ ∙ v)ᗮ.starProjection v) = 0
    rw [starProjection_orthogonalComplement_singleton_eq_zero, map_zero]
  have hgen : F (toLp 2 (u, (1 : ℝ))) = -G ((k : ℝ)⁻¹ • l) := by
    have he := congrArg F hv
    rw [hkill, map_add, map_smul, hhor] at he
    have he' : (k : ℝ) • F (toLp 2 (u, (1 : ℝ))) = -G l := eq_neg_of_add_eq_zero_right he.symm
    rw [map_smul, ← smul_neg, ← he', inv_smul_smul₀ hkR.ne']
  change (((appendWindow L u).map _).map _) = _
  rw [← Submodule.map_comp]
  change (appendWindow L u).map (F.restrictScalars ℤ) = (L ⊔ _).map (G.restrictScalars ℤ)
  rw [appendWindow, Submodule.map_sup, ← Submodule.map_comp, Submodule.map_sup, Submodule.map_span,
    Submodule.map_span, Set.image_singleton, Set.image_singleton]
  have hmaps : (F.restrictScalars ℤ).comp (horizontalInclusion.restrictScalars ℤ) =
      G.restrictScalars ℤ := LinearMap.ext hhor
  rw [hmaps]
  change _ ⊔ ℤ ∙ (F (toLp 2 (u, (1 : ℝ)))) = _ ⊔ ℤ ∙ (G ((k : ℝ)⁻¹ • l))
  rw [hgen, zspan_neg_singleton]

end SigabaNeo.Wall1

#print axioms SigabaNeo.Wall1.straighten_project_horizontal
#print axioms SigabaNeo.Wall1.verticalWinner_isometry
#print axioms SigabaNeo.Wall1.winnerCompression_norm_sq
