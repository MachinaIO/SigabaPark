import Definitions.Def_LatticeAttack_Research_Wall1_TerminalGridFrame

set_option autoImplicit true

/-! # Intrinsic determinant in an append-and-project step -/

noncomputable section
namespace SigabaNeo.Wall1.TerminalProjection

open Module Submodule WithLp MeasureTheory DecoupledDecoder
open scoped RealInnerProductSpace

variable {V F : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

def transport (e : V ≃ₗᵢ[ℝ] F) (L : Submodule ℤ V) : Submodule ℤ F :=
  ZLattice.comap ℝ L e.symm.toContinuousLinearEquiv.toLinearMap

instance (e : V ≃ₗᵢ[ℝ] F) (L : Submodule ℤ V) [DiscreteTopology L] :
    DiscreteTopology (transport e L) := by unfold transport; infer_instance

instance (e : V ≃ₗᵢ[ℝ] F) (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L] :
    IsZLattice ℝ (transport e L) := by unfold transport; infer_instance

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ F] in
theorem transport_eq (e : V ≃ₗᵢ[ℝ] F) (L : Submodule ℤ V) :
    transport e L = L.map (e.toLinearEquiv.toLinearMap.restrictScalars ℤ) := by
  ext x
  change e.symm x ∈ L ↔ ∃ y ∈ L, e y = x
  constructor
  · exact fun h ↦ ⟨_, h, e.apply_symm_apply x⟩
  · rintro ⟨y, hy, rfl⟩
    simpa

theorem transport_covolume [MeasurableSpace V] [BorelSpace V] [MeasurableSpace F] [BorelSpace F]
    (e : V ≃ₗᵢ[ℝ] F) (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L] :
    ZLattice.covolume (transport e L) = ZLattice.covolume L :=
  ZLattice.covolume_comap _ volume volume e.symm.measurePreserving

theorem covolume_append [MeasurableSpace V] [BorelSpace V]
    (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L] (u : V) :
    ZLattice.covolume (appendWindow L u) = ZLattice.covolume L := by
  classical
  let b := (Module.finBasis ℤ L).ofZLatticeBasis ℝ L
  let h := fun i ↦ horizontalInclusion (b i)
  let w : WindowSpace V := toLp 2 (u, 1)
  let c := Fin.snoc (α := fun _ ↦ WindowSpace V) h w
  have hspan : span ℝ (Set.range h) = horizontalInclusion.range := by
    change span ℝ (Set.range (horizontalInclusion ∘ ⇑b)) = _
    rw [Set.range_comp, ← map_span, b.span_eq, Submodule.map_top]
  have hproj : prefixProjection h w = toLp 2 (0, 1) := by
    unfold prefixProjection
    apply eq_starProjection_of_mem_of_inner_eq_zero
    · rw [hspan]
      intro y hy
      obtain ⟨z, rfl⟩ := hy
      change ⟪z, (0 : V)⟫ + (1 : ℝ) * 0 = 0
      simp
    · intro y hy
      have hh : horizontalInclusion u ∈ span ℝ (Set.range h) := hspan ▸ ⟨u, rfl⟩
      have he : w - toLp 2 ((0 : V), (1 : ℝ)) = horizontalInclusion u := by
        apply (WithLp.equiv 2 _).injective
        exact Prod.ext (sub_zero _) (sub_self _)
      simpa only [he] using hy _ hh
  have gram : Matrix.gram ℝ h = Matrix.gram ℝ b := by
    ext i j
    change ⟪b i, b j⟫ + (0 : ℝ)*0 = _
    simp [Matrix.gram_apply]
  have det : (Matrix.gram ℝ c).det = (Matrix.gram ℝ b).det := by
    rw [← projectedLength_sq_mul_det, hproj, gram]
    simp [WithLp.norm_toLp_snd]
  have li := (Matrix.det_gram_ne_zero_iff_linearIndependent (𝕜 := ℝ) (v := c)).1
    (det ▸ (Matrix.posDef_gram_of_linearIndependent b.linearIndependent).det_pos.ne')
  let d := basisOfLinearIndependentOfCardEqFinrank' c li (by
    rw [(WithLp.linearEquiv 2 ℝ (V × ℝ)).finrank_eq, Module.finrank_prod, Module.finrank_self]
    simp [ZLattice.rank ℝ L])
  have hd : ⇑d = c := Basis.coe_mk ..
  have hb := (Module.finBasis ℤ L).ofZLatticeBasis_span ℝ
  have he : span ℤ (Set.range d) = appendWindow L u := by
    rw [hd, Fin.range_snoc, span_insert, appendWindow, sup_comm]
    congr 1
    change span ℤ (Set.range ((horizontalInclusion.restrictScalars ℤ) ∘ ⇑b)) = _
    rw [Set.range_comp, ← map_span, hb]
  apply (sq_eq_sq₀ ENNReal.toReal_nonneg ENNReal.toReal_nonneg).mp
  have hwvol := covolume_span_sq_eq_gram d
  have hlvol := covolume_span_sq_eq_gram b
  rw [he, hd] at hwvol
  rw [hb] at hlvol
  exact hwvol.trans (det.trans hlvol.symm)

omit [FiniteDimensional ℝ V] in
/-- Shortestness makes every lattice point in the projection kernel an integral
multiple of the chosen signed vector. -/
theorem integer_kernel_of_shortest (L : Submodule ℤ V) {v w : V} (hv : IsShortest L v)
    (hw : w ∈ L) (hz : (ℝ ∙ v)ᗮ.starProjection w = 0) : ∃ k : ℤ, w = k • v := by
  obtain ⟨k, _, hb⟩ := roundedLift_sq v w
  refine ⟨k, sub_eq_zero.mp ?_⟩
  by_contra h
  have hs := hv.2.2 _ (L.sub_mem hw (L.smul_mem _ hv.1)) h
  rw [hz, norm_zero, zero_pow (by decide), zero_add] at hb
  have hp := norm_pos_iff.mpr hv.2.1
  nlinarith [(sq_le_sq₀ hp.le (norm_nonneg _)).mpr hs, sq_pos_of_pos hp]

/-- Projecting off a signed shortest vector divides intrinsic covolume by its norm. -/
theorem covolume_project_shortest [MeasurableSpace V] [BorelSpace V]
    (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L] {v : V}
    (hv : IsShortest L v) :
    ZLattice.covolume (projectedModule L (ℝ ∙ v)ᗮ) = ZLattice.covolume L / ‖v‖ := by
  classical
  let S := (ℝ ∙ v)ᗮ
  let Q := projectedModule L S
  let : DiscreteTopology Q := projectedModule_discrete _ hv.1
  let : IsZLattice ℝ Q := projectedModule_isZLattice _ hv.1
  let b := (Module.finBasis ℤ Q).ofZLatticeBasis ℝ Q
  have hb : span ℤ (Set.range b) = Q := (Module.finBasis ℤ Q).ofZLatticeBasis_span ℝ
  have hlift (i) : ∃ x ∈ L, S.orthogonalProjectionOnto x = b i := by
    have hi := subset_span (R := ℤ) (Set.mem_range_self (f := ⇑b) i)
    rw [hb] at hi
    exact hi
  choose a ha he using hlift
  let c := Fin.cons (α := fun _ ↦ V) v a
  let C := span ℤ (Set.range c)
  have hC : C = ℤ ∙ v ⊔ span ℤ (Set.range a) := by simp [C, c, Fin.range_cons, span_insert]
  have hCL : C ≤ L := by
    rw [hC]
    exact sup_le ((span_singleton_le_iff_mem _ _).2 hv.1)
      (span_le.mpr (by rintro _ ⟨i, rfl⟩; exact ha i))
  have himg : projectedModule C S = Q := by
    apply le_antisymm (Submodule.map_mono hCL)
    apply hb.ge.trans
    apply span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact ⟨a i, (by rw [hC]; exact mem_sup_right (subset_span (Set.mem_range_self i))), he i⟩
  have eqL : C = L := by
    refine le_antisymm hCL fun w hw ↦ ?_
    have hwQ : S.orthogonalProjectionOnto w ∈ projectedModule C S := himg ▸ ⟨w, hw, rfl⟩
    obtain ⟨z, hz, hz'⟩ := hwQ
    have hzero : S.starProjection (w-z) = 0 := by
      change (S.orthogonalProjectionOnto (w-z)).val = 0
      rw [map_sub, ← (show S.orthogonalProjectionOnto z = S.orthogonalProjectionOnto w from hz')]
      simp
    obtain ⟨k, hk⟩ := integer_kernel_of_shortest L hv (L.sub_mem hw (hCL hz)) hzero
    rw [sub_eq_iff_eq_add.mp hk]
    exact C.add_mem (C.smul_mem _ (hC ▸ mem_sup_left (mem_span_singleton_self _))) hz
  have hg : (Matrix.gram ℝ c).det = ‖v‖^2 * (Matrix.gram ℝ b).det := by
    rw [det_gram_project_tail]
    simp only [c, Fin.cons_zero, Fin.cons_succ]
    congr 2
    ext i j
    change ⟪S.orthogonalProjectionOnto (a i), S.orthogonalProjectionOnto (a j)⟫ = _
    rw [he, he]
    rfl
  have hp := norm_pos_iff.mpr hv.2.1
  have li := (Matrix.det_gram_ne_zero_iff_linearIndependent (𝕜 := ℝ) (v := c)).1
    (hg ▸ (mul_pos (sq_pos_of_pos hp)
      (Matrix.posDef_gram_of_linearIndependent b.linearIndependent).det_pos).ne')
  let d := basisOfLinearIndependentOfCardEqFinrank' c li (by
    have hr := (ℝ ∙ v).finrank_add_finrank_orthogonal
    rw [finrank_span_singleton hv.2.1] at hr
    simp only [Fintype.card_fin, ZLattice.rank ℝ Q]
    change finrank ℝ S + 1 = _
    exact (Nat.add_comm _ _).trans hr)
  have hd : ⇑d = c := Basis.coe_mk ..
  have eqd : span ℤ (Set.range d) = L := hd ▸ eqL
  apply (eq_div_iff hp.ne').mpr
  apply (sq_eq_sq₀ (mul_nonneg ENNReal.toReal_nonneg hp.le) ENNReal.toReal_nonneg).mp
  change (ZLattice.covolume Q * ‖v‖)^2 = _
  have hQ := covolume_span_sq_eq_gram b
  have hL := covolume_span_sq_eq_gram d
  rw [hb] at hQ
  rw [eqd, hd, hg] at hL
  rw [mul_pow, hQ, mul_comm]
  exact hL.symm


end SigabaNeo.Wall1.TerminalProjection
#print axioms SigabaNeo.Wall1.TerminalProjection.covolume_append
#print axioms SigabaNeo.Wall1.TerminalProjection.transport_covolume

#print axioms SigabaNeo.Wall1.TerminalProjection.covolume_project_shortest
