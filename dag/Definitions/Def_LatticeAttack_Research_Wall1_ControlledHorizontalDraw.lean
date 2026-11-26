import Definitions.Def_LatticeAttack_Research_Wall1_ControlledTernaryCap
import Definitions.Def_LatticeAttack_Research_Wall1_ControlledPhysicalDraw

set_option autoImplicit true

/-! The actual fresh-height witness after a horizontal win, including frame transport. -/
noncomputable section
namespace SigabaNeo.Wall1.ControlledPlane
open TerminalProjection TerminalProjection.Restart506 TerminalProjection.ChainState
open Real Submodule DecoupledDecoder DualExit WithLp
open scoped RealInnerProductSpace Classical
local instance : Fact (Nat.Prime 3329) := ⟨by norm_num⟩

private def dropMap {n d : ℕ} (s : ChainState n (CoordSpace (d+1))) :
    CoordSpace (d+1) →ₗ[ℝ] CoordSpace d :=
  let S := (ℝ ∙ s.winner)ᗮ
  let e := ChainState.coord (d:=d) (V:=S) (by
    have h := (ℝ ∙ s.winner).finrank_add_finrank_orthogonal
    rw [finrank_span_singleton s.shortest.2.1,finrank_euclideanSpace_fin] at h
    change 1 + Module.finrank ℝ S = d+1 at h
    omega)
  e.toLinearEquiv.toLinearMap.comp S.orthogonalProjectionOnto.toLinearMap

private theorem freeze_image {d n : ℕ} (s : ChainState n (CoordSpace (d+1))) :
    s.freeze.M = s.M.map ((dropMap s).restrictScalars ℤ) := by
  dsimp only [freeze, reframe, project]
  rw [transport_eq,projectedModule,← Submodule.map_comp]
  rfl

private theorem drop_norm {d n : ℕ} (s : ChainState n (CoordSpace (d+1))) (w : CoordSpace (d+1)) :
    ‖dropMap s w‖ = ‖(ℝ ∙ s.winner)ᗮ.starProjection w‖ := by
  unfold dropMap
  dsimp only [LinearMap.comp_apply,LinearEquiv.coe_coe,LinearIsometryEquiv.coe_toLinearEquiv,ContinuousLinearMap.coe_coe]
  rw [LinearIsometryEquiv.norm_map]
  rfl

private theorem drop_axis {d n : ℕ} (s : ChainState n (CoordSpace (d+1))) (w : CoordSpace (d+1))
    (i : Fin n) : ⟪s.freeze.frame.axis i,dropMap s w⟫ =
      ⟪s.frame.axis i,(ℝ ∙ s.winner)ᗮ.starProjection w⟫ := by
  unfold freeze reframe project dropMap
  dsimp only [AxisFrame.project,LinearMap.comp_apply,LinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toLinearEquiv,ContinuousLinearMap.coe_coe]
  rw [LinearIsometryEquiv.inner_map_map,inner_orthogonalProjectionOnto_eq_of_mem_right]
  rfl

private theorem horizontal_proj {d : ℕ} (x : CoordSpace d) (y : WindowSpace (CoordSpace d)) :
    (ℝ ∙ horizontalInclusion x)ᗮ.starProjection y =
      toLp 2 ((ℝ ∙ x)ᗮ.starProjection y.fst, y.snd) := by
  rw [starProjection_orthogonal_val,starProjection_singleton,starProjection_orthogonal_val,
    starProjection_singleton]
  have h : ⟪horizontalInclusion x,y⟫ = ⟪x,y.fst⟫ := by
    change ⟪x,y.fst⟫+y.snd*0 = _
    ring
  rw [h,show ‖horizontalInclusion x‖ = ‖x‖ from WithLp.norm_toLp_fst 2 _ _ _]
  apply (WithLp.equiv 2 _).injective
  exact Prod.ext rfl (by change y.snd - _ • (0:ℝ) = y.snd; simp)

private theorem commuted {d n : ℕ} (s : ChainState n (CoordSpace (d+1))) (c : Column)
    (ho : (s.append c).winner.snd = 0) (y : WindowSpace (CoordSpace (d+1))) :
    let W := incoming s c
    let e := windowCoord (d+1)
    (ℝ ∙ W.winner)ᗮ.starProjection (e y) =
      e (toLp 2 ((ℝ ∙ s.winner)ᗮ.starProjection y.fst,y.snd)) := by
  intro W e
  have agree := agreement_of_order (s.append c).key (s.append c).key_injective s.shortest
    (s.append c).shortest (fun a ha ↦ s.key_horizontal_le c ((chosen_spec s.key s.M s.nonbot).2 a ha))
    (chosen_spec (s.append c).key (s.append c).M (s.append c).nonbot).2 ho
  have he : (ℝ ∙ (s.append c).winner)ᗮ.map e.toLinearEquiv.toLinearMap = (ℝ ∙ W.winner)ᗮ := by
    rw [map_orthogonal_equiv,map_span,Set.image_singleton]
    unfold W incoming
    rw [reframe_winner]
    rfl
  have h := starProjection_map_apply e (ℝ ∙ (s.append c).winner)ᗮ (e y)
  simp only [he,e.symm_apply_apply] at h
  simpa only [agree,horizontal_proj] using h

private theorem forced_vector {n : ℕ} (s : ChainState n (CoordSpace 505)) (c : Column)
    (ho : (s.append c).winner.snd = 0) {v : CoordSpace 505}
    (hv : v ∈ (incoming s c).freeze.M)
    (hf : ⟪(incoming s c).freeze.frame.axis (Fin.last n),v⟫ ≠ 0)
    {r : ℝ} (hr : ‖v‖ ≤ r) :
    PositiveHit s.freeze.M (columnLift s.freeze.g c) r := by
  let W := incoming s c
  let e := windowCoord 505
  rw [freeze_image] at hv
  obtain ⟨y',hy,rfl⟩ := hv
  obtain ⟨y,rfl⟩ := e.surjective y'
  have hm : y ∈ appendWindow s.M (columnLift s.g c) := by
    change e.symm (e y) ∈ (s.append c).M at hy
    rwa [e.symm_apply_apply] at hy
  let t : WindowSpace (CoordSpace 504) := toLp 2 (dropMap s y.fst,y.snd)
  have hcomm := commuted s c ho y
  have hn : ‖t‖ = ‖dropMap W (e y)‖ := by
    rw [drop_norm,hcomm,e.norm_map]
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [WithLp.prod_norm_sq_eq_of_L2,WithLp.prod_norm_sq_eq_of_L2]
    change ‖dropMap s y.fst‖^2 + _ = _
    rw [drop_norm]
    rfl
  have hheight : y.snd ≠ 0 := by
    intro h0
    apply hf
    change ⟪W.freeze.frame.axis (Fin.last n),dropMap W (e y)⟫ = 0
    rw [drop_axis,hcomm]
    change ⟪e (s.frame.append.axis (Fin.last n)), e _⟫ = 0
    rw [e.inner_map_map]
    simp only [AxisFrame.append,Fin.snoc_last]
    change ⟪(0:CoordSpace 505),_⟫ + y.snd * 1 = 0
    simp [h0]
  obtain ⟨j,hj⟩ := integral_height hm
  have ht : t ∈ appendWindow s.freeze.M (columnLift s.freeze.g c) := by
    apply (mem_append_at_height _ _ t j hj).2
    rw [← map_zsmul]
    apply (Submodule.Quotient.eq _).2
    have hm' := (mem_append_at_height _ _ _ _ hj).1 hm
    rw [← map_zsmul] at hm'
    have hm' := (Submodule.Quotient.eq _).1 hm'
    rw [freeze_image]
    refine ⟨_,hm',?_⟩
    change dropMap s (y.fst-j • columnLift s.g c) = dropMap s y.fst-j • columnLift s.freeze.g c
    rw [map_sub,map_zsmul]
    congr 2
    unfold columnLift
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_nsmul]
    rfl
  have hnorm : ‖t‖ ≤ r := hn.trans_le hr
  rcases lt_or_gt_of_ne hheight with h | h
  · exact ⟨-t,(appendWindow _ _).neg_mem ht,neg_pos.mpr h,by simpa using hnorm⟩
  · exact ⟨t,ht,h,hnorm⟩

private theorem horizontal_old_le {n : ℕ} (s : ChainState n (CoordSpace 505)) (c : Column)
    (ho : (s.append c).winner.snd = 0) : ‖s.winner‖ ≤ ‖(incoming s c).winner‖ := by
  let w := (s.append c).winner
  have he : horizontalInclusion w.fst = w := (WithLp.equiv 2 _).injective (Prod.ext rfl ho.symm)
  have hm := (mem_append_at_height _ _ w 0 (by simpa using ho)).1 (s.append c).shortest.1
  have hh := s.shortest.2.2 w.fst ((Submodule.Quotient.mk_eq_zero _).mp (by simpa using hm))
    (fun h ↦ (s.append c).shortest.2.1 (he.symm.trans ((congrArg _ h).trans (map_zero _))))
  unfold incoming
  rw [reframe_winner,LinearIsometryEquiv.norm_map]
  exact hh.trans_eq ((WithLp.norm_toLp_fst 2 _ _ w.fst).symm.trans (congrArg norm he))

/-- With a physical incoming determinant bound the forced horizontal projection
costs one winner length in the denominator and preserves the fresh height. -/
theorem horizontalCase_gaussian (t : Fin 406) {l : ℝ}
    (floor : ∀ h, exp l ≤ ZLattice.covolume (retained h t.val).M) :
    probability (horizontalCase t.val) ≤ ballCharge 505 planeRadius (l-log winnerRadius) := by
  have hR : 0 < winnerRadius := by unfold winnerRadius areaCut; positivity
  have hr : 0 < planeRadius := by unfold planeRadius areaCut; positivity
  have hq : planeRadius < 3329 := by
    unfold planeRadius areaCut
    rw [mul_div_assoc',div_div,← sq,sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]
    exact (sqrt_lt' (by norm_num)).mpr (by norm_num)
  let E := fun (s : ChainState (505+t.val) (CoordSpace 505)) (c : Column) ↦
    ‖s.winner‖ ≤ winnerRadius ∧ PositiveHit s.freeze.M (columnLift s.freeze.g c) planeRadius
  apply le_trans _ (adaptive_draw_bound t E ?_)
  · apply probability_mono
    intro A ha
    obtain ⟨ho,b,hp,hb,v,hv,hf⟩ := ha
    let h := history A
    let s := retained h t.val
    let c := past h (105+t.val)
    have ho' : (s.append c).winner.snd = 0 := by
      simpa [horizontalWinner,window,incoming,reframe_winner,h,s,c] using ho
    have hc := hit_winner_cap h t.val ⟨b,hp,hb⟩
    refine ⟨(horizontal_old_le s c ho').trans hc,forced_vector s c ho' ?_ hf ?_⟩
    · exact (span_le.mpr (Set.range_subset_iff.mpr b.mem)) hv.1
    · obtain ⟨x,hx,hx0,hlen⟩ := short_in_span b.vec b.ind
      apply (hv.2.2 x hx hx0).trans
      have ha' : 0 < areaCut := by unfold areaCut; positivity
      have hA : sqrt (Matrix.gram ℝ b.vec).det ≤ areaCut := (ENNReal.ofReal_le_ofReal_iff ha'.le).mp hb
      apply le_sqrt_of_sq_le
      apply (le_div_iff₀ (by positivity : 0 < sqrt 3)).mpr
      linarith
  · intro h
    let s := retained h t.val
    by_cases hc : ‖s.winner‖ ≤ winnerRadius
    · have hd : exp (l-log winnerRadius) ≤ ZLattice.covolume s.freeze.M := by
        rw [freeze_covolume,exp_sub,exp_log hR]
        exact div_le_div₀ (ZLattice.covolume_pos s.M _).le (floor h) (norm_pos_iff.mpr s.shortest.2.1) hc
      simpa only [E,s,hc,true_and] using (column_positive_bound s.freeze hq).trans
        (candidateRatio_le_ballCharge s.freeze hr hd)
    · change mass (fun c ↦ ‖s.winner‖ ≤ _ ∧ _) ≤ _
      simp only [hc,false_and,mass,Finset.filter_false,Finset.card_empty,Nat.cast_zero,zero_div]
      have z := mul_pos hr (sqrt_pos.mpr (by positivity : 0 < 2*π/(505:ℝ)))
      have hθ := (tsum_nonneg fun _ ↦ (exp_pos _).le).trans (integerGaussian_le_terminalTheta z)
      unfold ballCharge
      norm_num only [Nat.cast_ofNat]
      positivity

end SigabaNeo.Wall1.ControlledPlane

#print axioms SigabaNeo.Wall1.ControlledPlane.horizontalCase_gaussian
