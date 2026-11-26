import Definitions.Def_LatticeAttack_Research_Wall1_HaarMinimumTails

set_option autoImplicit true

/-! Part 105: the deterministic acceptance cutoff and the ambient Haar minimum CDF.
The marked-lattice disintegration and the character average defining the void probability
are still needed to integrate the cutoff against the selected quotient law. -/

noncomputable section
open MeasureTheory Submodule
open scoped ENNReal InnerProductSpace
namespace SigabaNeo.Wall1

/-- Rounding a lift along a shortest vector bounds every nonzero projected length. -/
theorem shortest_projection_gap {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (L : AddSubgroup F) {v : F} (hv : v ∈ L) (_hv0 : v ≠ 0)
    (hmin : ∀ u ∈ L, u ≠ 0 → ‖v‖ ≤ ‖u‖) {w : F} (hw : w ∈ L) :
    (ℝ ∙ v)ᗮ.starProjection w = 0 ∨
      Real.sqrt 3 / 2 * ‖v‖ ≤ ‖(ℝ ∙ v)ᗮ.starProjection w‖ := by
  classical
  let S := ℝ ∙ v
  change Sᗮ.starProjection w = 0 ∨ _
  by_cases hz : Sᗮ.starProjection w = 0
  · exact Or.inl hz
  right
  obtain ⟨a, ha⟩ := mem_span_singleton.mp (S.starProjection_apply_mem w)
  let k := round (a : ℝ)
  let u := w - k • v
  have hp : Sᗮ.starProjection u = Sᗮ.starProjection w := by
    simp only [u, map_sub, map_zsmul, S, starProjection_orthogonalComplement_singleton_eq_zero,
      zsmul_zero, sub_zero]
  have hu : u ≠ 0 := fun h ↦ hz (by rw [← hp, h, map_zero])
  have hm := hmin u (L.sub_mem hw (L.zsmul_mem hv k)) hu
  have hs : S.starProjection u = (a - (k : ℝ)) • v := by
    have hfix : S.starProjection v = v := starProjection_eq_self_iff.mpr (mem_span_singleton_self v)
    simp only [u, map_sub, map_zsmul, hfix, ← ha, sub_smul, Int.cast_smul_eq_zsmul]
  have py := norm_sq_eq_add_norm_sq_starProjection u S
  rw [hp, hs, norm_smul, Real.norm_eq_abs] at py
  have hr := mul_le_mul_of_nonneg_right (abs_sub_round a) (norm_nonneg v)
  change |a - (k : ℝ)| * ‖v‖ ≤ _ at hr
  change Real.sqrt 3 / 2 * ‖v‖ ≤ ‖Sᗮ.starProjection w‖
  apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) (norm_nonneg _)
  nlinarith [sq_le_sq' (by linarith [norm_nonneg u, norm_nonneg v] : -‖u‖ ≤ ‖v‖) hm,
    pow_le_pow_left₀ (mul_nonneg (abs_nonneg _) (norm_nonneg _)) hr 2,
    congrArg (fun t : ℝ ↦ t * ‖v‖ ^ 2) (Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3))]

open SigabaNeo.Rogers

/-- The strict first-minimum event is witnessed by any nonzero integer coordinate vector.
Dividing its coordinates by their content produces a primitive witness in the same open ball. -/
theorem haar_short_vector_upper {n : ℕ} (hn : 2 ≤ n) (D : Set (SL n))
    (hm : MeasurableSet D) (hd : IsFundamentalDomain (integerGroup n).op D (groupHaar n))
    (hp : groupHaar n D ≠ 0) (hf : groupHaar n D ≠ ⊤) {r : ℝ} (hr : 0 < r) :
    (groupHaar n).restrict D {g | ∃ z : NonzeroIntVector n,
      ‖WithLp.toLp 2 (g • fun j ↦ (z.val j : ℝ))‖ < r} / groupHaar n D ≤
      ENNReal.ofReal (r ^ n) * volume (Metric.ball (0 : E n) 1) /
        (2 * ∑' k, dilationWeight n k) := by
  classical
  have upper := primitiveBallPairs_hit_upper hn D hm hd hp hf r
  rw [Measure.addHaar_ball_of_pos volume _ hr, finrank_euclideanSpace, Fintype.card_fin] at upper
  refine le_trans (ENNReal.div_le_div_right (measure_mono ?_) _) upper
  rintro g ⟨z, hz⟩
  let c := vectorContent z
  obtain ⟨p, he⟩ := (scalePrimitive_bijective (vectorContent_ne_zero z)).surjective ⟨z, rfl⟩
  let x : E n := WithLp.toLp 2 (g • fun j ↦ (p.val.val j : ℝ))
  have eqv : WithLp.toLp 2 (g • fun j ↦ (z.val j : ℝ)) = (c : ℝ) • x := by
    apply WithLp.ofLp_injective 2
    change g.val.mulVec _ = (c : ℝ) • g.val.mulVec _
    rw [← Matrix.mulVec_smul]
    congr 1
    funext i
    have hi := congrArg (fun q : ContentFiber n c ↦ q.val.val i) he
    change (c : ℤ) * p.val.val i = z.val i at hi
    simp [← hi]
  rw [eqv, norm_smul, Real.norm_natCast] at hz
  have hc : (1 : ℝ) ≤ c := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (vectorContent_ne_zero z)
  have hx : x ∈ Metric.ball 0 r := by
    simpa using lt_of_le_of_lt (le_mul_of_one_le_left (norm_nonneg x) hc) hz
  unfold primitiveBallPairs
  apply ENNReal.mul_pos (by simp)
  apply ne_of_gt
  apply lt_of_lt_of_le _ (le_tsum _ p)
  change 0 < (Metric.ball (0 : E n) r).indicator (1 : E n → ℝ≥0∞) x
  simp [Set.indicator_of_mem hx]

#print axioms shortest_projection_gap
#print axioms haar_short_vector_upper
end SigabaNeo.Wall1
