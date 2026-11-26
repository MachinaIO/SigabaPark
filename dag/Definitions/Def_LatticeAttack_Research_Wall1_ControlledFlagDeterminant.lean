import Definitions.Def_LatticeAttack_Research_Wall1_ControlledFlagEnvelope

set_option autoImplicit true

/-! Determinant accounting for the skipped part of a last-coordinate flag. -/

noncomputable section
namespace SigabaNeo.Wall1.ControlledPlane
open TerminalProjection TerminalProjection.Restart506 Real Finset DualExit

/-- The successive signed old winners in the forced suffix obey their respective
length caps, starting at tail length k. -/
def ForcedLengths {n d : ℕ} : (j k : ℕ) → ChainState n (CoordSpace (d+j)) → Prop
  | 0, _, _ => True
  | j+1, k, s => ‖s.winner‖ ≤ planeRadius * flagCap k ∧ ForcedLengths j (k-1) s.freeze

private theorem cap_pos (k : ℕ) : 0 < flagCap k := by
  induction k with
  | zero => exact zero_lt_one
  | succ k ih => exact ih.trans_le (le_max_left ..)

/-- Peeling j forced winners loses at most the log-cap difference and j copies
of the terminal log radius. -/
theorem forced_log_covolume {n d : ℕ} (j k : ℕ) (hjk : j ≤ k)
    (s : ChainState n (CoordSpace (d+j))) (h : ForcedLengths j k s) :
    log (ZLattice.covolume s.M)-logCaps k+logCaps (k-j)-j*log planeRadius ≤
      log (ZLattice.covolume (forceOld j s).M) := by
  induction j generalizing k with
  | zero => simp [forceOld]
  | succ j ih =>
    obtain ⟨hw,hl⟩ := h
    obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show k ≠ 0 by omega)
    have step := ih k (by omega) s.freeze hl
    rw [ChainState.freeze_covolume,log_div (ZLattice.covolume_pos s.M _).ne'
      (norm_pos_iff.mpr s.shortest.2.1).ne'] at step
    have hm := log_le_log (norm_pos_iff.mpr s.shortest.2.1) hw
    rw [log_mul (by unfold planeRadius areaCut; positivity) (cap_pos _).ne'] at hm
    have he : logCaps (k+1) = logCaps k+log (flagCap (k+1)) := sum_Icc_succ_top (by omega) _
    simp only [he, Nat.succ_sub_succ_eq_sub, Nat.cast_succ,forceOld]
    linarith

private theorem cast_covol {m a b : ℕ} (e : a = b) (s : ChainState (b+m) (CoordSpace b)) :
    let t : ChainState (a+m) (CoordSpace a) := e ▸ s
    ZLattice.covolume t.M = ZLattice.covolume s.M := by
  subst b
  rfl

/-- The explicit last-draw witness needs no separate determinant-guard proof
once its forced lengths and the incoming physical floor have been supplied. -/
theorem flagTest_of_lengths (u : FlagIndex) (h : History)
    (floor : terminalLogFloor u.1.val ≤ log (ZLattice.covolume (retained h u.1.val).M)) :
    let j := u.2.val
    let k := 155-u.1.val
    have he : 505-j+j = 505 := by dsimp [j]; omega
    let s := Eq.rec (motive := fun a _ ↦ ChainState (a+u.1.val) (CoordSpace a))
      (retained h u.1.val) he.symm
    ForcedLengths (d:=505-j) j k s →
    PositiveHit (forceOld j s).M (columnLift (forceOld j s).g (past h (105+u.1.val)))
      (flagRadius u) → flagTest flagRadius flagFloor u h := by
  intro j k he s hl hp
  refine ⟨?_,hp⟩
  have hh := forced_log_covolume (d:=505-j) j k (by dsimp [j,k]; omega) s hl
  have hd : ZLattice.covolume s.M = ZLattice.covolume (retained h u.1.val).M :=
    cast_covol he (retained h u.1.val)
  rw [hd] at hh
  apply (exp_le_exp.mpr _).trans_eq (exp_log (ZLattice.covolume_pos (forceOld j s).M _))
  unfold flagFloor
  dsimp only at *
  linarith

/-- Unconditional candidate-probability field of Part 192. -/
theorem prefix_ball (u : FlagIndex) :
    @probability 400 512 3329 ⟨by norm_num⟩
      (fun A ↦ flagTest flagRadius flagFloor u (history A)) ≤ flagCharge u :=
  flag_probability u (FlagEnvelope.radius_lt_modulus u)

end SigabaNeo.Wall1.ControlledPlane

#print axioms SigabaNeo.Wall1.ControlledPlane.forced_log_covolume
#print axioms SigabaNeo.Wall1.ControlledPlane.flagTest_of_lengths
#print axioms SigabaNeo.Wall1.ControlledPlane.prefix_ball
