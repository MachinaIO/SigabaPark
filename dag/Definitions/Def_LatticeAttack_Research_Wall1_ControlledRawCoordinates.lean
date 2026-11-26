import Definitions.Def_LatticeAttack_Research_Wall1_ControlledFlagEnvelope

set_option autoImplicit true

/-! Read a short vector of the initial retained state back as an integer witness
for the original design, through the coordinate changes of the 105 appends. -/

noncomputable section
namespace SigabaNeo.Wall1.ControlledPlane
open TerminalProjection TerminalProjection.Restart506 TerminalProjection.ChainState
open Submodule Module Finset DualExit WithLp
open scoped Classical
local instance : Fact (Nat.Prime 3329) := ⟨by norm_num⟩

private def markShift {d n : ℕ} (s : ChainState n (CoordSpace d)) (a : Fin 400 → ℤ) :=
  ∑ i, a i • s.g i

/-- Keep an integral shift of the 400 output generators while reading the
append operations backwards. This accounts for each column multiplied by its
integer height. -/
private theorem graph_coordinates (h : History) (t : ℕ) (y : CoordSpace (400+t))
    (hy : y ∈ (graphPrefix h t).M) (a : Fin 400 → ℤ) :
    ∃ (o : Fin 400 → ℤ) (v : Fin t → ℤ),
      ‖y+markShift (graphPrefix h t) a‖^2 = sqLength o + sqLength v ∧
      ∀ i, (o i : ZMod 3329) = a i + ∑ j, (v j : ZMod 3329)*past h j.val i := by
  induction t generalizing a with
  | zero =>
    let b := EuclideanSpace.basisFun (Fin 400) ℝ
    let B := b.toBasis.isUnitSMul (w := fun _ ↦ (3329:ℝ))
      (fun _ ↦ isUnit_iff_ne_zero.2 (by norm_num))
    change y ∈ span ℤ (Set.range B) at hy
    obtain ⟨k,rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hy
    let o (i : Fin 400) := 3329*k i+a i
    refine ⟨o,Fin.elim0,?_,?_⟩
    · have em : markShift (graphPrefix h 0) a = ∑ i, a i • b i := rfl
      rw [em,EuclideanSpace.real_norm_sq_eq]
      simp only [sqLength,Finset.univ_eq_empty,Finset.sum_empty,add_zero]
      apply sum_congr rfl
      intro i _
      congr 1
      simp [B,Basis.isUnitSMul_apply,b,EuclideanSpace.basisFun_apply,o,
        ← Int.cast_smul_eq_zsmul ℝ,Pi.single_apply, mul_ite, ite_mul, eq_comm]
      <;> ring
    · intro i; simp [o,show (3329:ZMod 3329) = 0 by decide +kernel]
  | succ t ih =>
    let s := graphPrefix h t
    let c := past h t
    let e := windowCoord (400+t)
    obtain ⟨w,rfl⟩ := e.surjective y
    change e.symm (e w) ∈ (s.append c).M at hy
    rw [e.symm_apply_apply] at hy
    obtain ⟨j,hj⟩ := integral_height hy
    have hm := (mem_append_at_height _ _ _ j hj).1 hy
    rw [← map_zsmul] at hm
    have hl := (Submodule.Quotient.eq _).1 hm
    let a' (i : Fin 400) := a i+j*(c i).val
    obtain ⟨o,v,hN,hA⟩ := ih _ hl a'
    refine ⟨o,Fin.snoc v j,?_,?_⟩
    · have he : markShift (graphPrefix h (t+1)) a =
          e (horizontalInclusion (markShift s a)) := by
        unfold markShift
        simp only [map_sum,map_zsmul]
        rfl
      have add : markShift s a' = markShift s a + j • columnLift s.g c := by
        simp only [markShift,a',add_smul,Finset.sum_add_distrib,columnLift,Finset.smul_sum,
          mul_smul,natCast_zsmul]
      rw [add,sub_add_add_cancel] at hN
      rw [he,← map_add,e.norm_map,WithLp.prod_norm_sq_eq_of_L2]
      change ‖w.fst+markShift s a‖^2+‖w.snd+0‖^2 = _
      rw [hN,add_zero,hj,Real.norm_eq_abs,sq_abs]
      unfold sqLength
      conv_rhs => rhs; rw [Fin.sum_univ_castSucc]
      simp [add_assoc]
    · intro i
      rw [hA,Fin.sum_univ_castSucc]
      simp only [a',Int.cast_add,Int.cast_mul,Int.cast_natCast,ZMod.natCast_zmod_val,
        Fin.snoc_castSucc,Fin.snoc_last,Fin.val_castSucc,Fin.val_last,c]
      ring

/-- The entirely old prefix alternative, stated for any length bound on the
lifted vector. In particular the draw-zero incidence is unconditional. -/
theorem rawShort_of_initial {r : ℝ} (A : Sample) {w : CoordSpace 505}
    (hw : w ∈ (retained (history A) 0).M) (hn : w ≠ 0) (hr : ‖w‖ ≤ r) :
    rawShort (designPrefix (by decide : 105 ≤ 512) A) r := by
  obtain ⟨o,v,hN,hA⟩ := graph_coordinates (history A) 105 w hw 0
  simp only [markShift,Pi.zero_apply,zero_smul,sum_const_zero,add_zero] at hN
  let z : Grid 400 105 := Sum.elim o v
  have E : sqLength z = ‖w‖^2 := by
    rw [hN]
    simp [sqLength,z,Fintype.sum_sum_type]
  refine ⟨z,?_,E.trans_le (pow_le_pow_left₀ (norm_nonneg _) hr 2),?_⟩
  · intro h
    rw [h] at E
    simp [sqLength] at E
    exact (sq_pos_of_pos (norm_pos_iff.mpr hn)).ne E
  · funext i
    change (∑ j : Fin 105, A i (Fin.castLE (by decide) j) * (v j : ZMod 3329)) = (o i : ZMod 3329)
    rw [hA]; simp only [Pi.zero_apply,Int.cast_zero,zero_add]
    apply sum_congr rfl
    intro j _
    rw [mul_comm]
    simp only [past,dite_eq_left (show j.val < 511 by omega),history]
    rfl

/-- The Part 192 cap at every possible initial flag length fits the raw
radius-2885 test, with the actual terminal plane radius. -/
theorem initial_flag_radius (k : ℕ) (hk : k ≤ 155) : planeRadius * flagCap k ≤ 2885 := by
  have check : ∀ i : Fin 156, FlagEnvelope.logCap i ≤ 4.565027 := by decide +kernel
  have hl := (FlagEnvelope.log_flagCap k hk).trans
    ((Rat.cast_le (K := ℝ)).2 (check ⟨k,by omega⟩))
  have positive (i : ℕ) : 0 < flagCap i := by
    induction i with
    | zero => exact zero_lt_one
    | succ n ih => exact ih.trans_le (le_max_left ..)
  have hc := positive k
  have ht : flagCap k ≤ (1.76937854:ℝ)^8 := by
    rw [← Real.exp_log hc]
    apply (Real.exp_le_exp.mpr (by simpa using hl : Real.log (flagCap k) ≤ 4.565027)).trans
    rw [show (4.565027:ℝ) = (8:ℕ)*((4.565027/8:ℚ):ℝ) by norm_num,Real.exp_nat_mul]
    have h := TerminalInterval.exp_upper (4.565027/8) 1.76937854 (by decide +kernel)
      (by decide +kernel) (by decide +kernel)
    exact pow_le_pow_left₀ (Real.exp_pos _).le (by simpa using h) 8
  have hr : planeRadius ≤ 30.02222 := by
    unfold planeRadius areaCut
    rw [mul_div_assoc',div_div,← sq,Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]
    exact (Real.sqrt_le_left (by norm_num)).mpr (by norm_num)
  exact (mul_le_mul hr ht hc.le (by norm_num)).trans (by norm_num)

theorem rawShort_of_initial_flag (k : ℕ) (hk : k ≤ 155) (A : Sample) {w : CoordSpace 505}
    (hw : w ∈ (retained (history A) 0).M) (hn : w ≠ 0) (hr : ‖w‖ ≤ planeRadius * flagCap k) :
    rawShort (designPrefix (by decide : 105 ≤ 512) A) 2885 :=
  rawShort_of_initial A hw hn (hr.trans (initial_flag_radius k hk))

end SigabaNeo.Wall1.ControlledPlane

#print axioms SigabaNeo.Wall1.ControlledPlane.rawShort_of_initial
#print axioms SigabaNeo.Wall1.ControlledPlane.initial_flag_radius
#print axioms SigabaNeo.Wall1.ControlledPlane.rawShort_of_initial_flag
