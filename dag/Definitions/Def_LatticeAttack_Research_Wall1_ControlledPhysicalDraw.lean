import Definitions.Def_LatticeAttack_Research_Wall1_ControlledGaussianCandidates

set_option autoImplicit true

/-! Physical determinant requirements for the two positive-winner draw comparisons. -/

noncomputable section
namespace SigabaNeo.Wall1.ControlledPlane
open TerminalProjection TerminalProjection.Restart506 DualExit Real
open scoped Classical
local instance : Fact (Nat.Prime 3329) := ⟨by norm_num⟩

/-- The Gaussian comparison in any old rank, at its optimizing width. -/
theorem candidateRatio_le_ballCharge {n d : ℕ} (s : ChainState n (CoordSpace d))
    {r l : ℝ} (hr : 0 < r) (hD : exp l ≤ ZLattice.covolume s.M) :
    candidateRatio s r ≤ ballCharge (d+1) r l := by
  let z := r*sqrt (2*π/(d+1:ℝ))
  have hb : 0 < (d+1:ℝ) := by positivity
  have hz : 0 < z := by dsimp [z]; positivity
  have e : π*r^2/z^2 = (d+1:ℝ)/2 := by
    dsimp [z]; rw [mul_pow, sq_sqrt (by positivity)]; field_simp
  have h := candidateRatio_gaussian s hr.le hz
  rw [e] at h
  have ht := (tsum_nonneg fun _ ↦ (exp_pos _).le).trans (integerGaussian_le_terminalTheta hz)
  apply h.trans ((div_le_div_of_nonneg_left (by positivity) (exp_pos l) hD).trans_eq ?_)
  simp only [ballCharge,Nat.cast_add,Nat.cast_one,Nat.add_sub_cancel,exp_sub,z]
  ring

/-- A bound on the physical determinant suffices at the actual adaptive draw.
The result applies at both specified radii. -/
theorem positiveCase_gaussian (t : Fin 406) {r l : ℝ} (hr : 0 < r) (hq : r < 3329)
    (floor : ∀ h, exp l ≤ ZLattice.covolume (retained h t.val).M) :
    probability (positiveCase r t.val) ≤ ballCharge 506 r l := by
  let E := fun (s : ChainState (505+t.val) (CoordSpace 505)) (c : Column) ↦
    PositiveHit s.M (columnLift s.g c) r
  apply le_trans _ (adaptive_draw_bound t E fun h ↦
    (column_positive_bound _ hq).trans (candidateRatio_le_ballCharge _ hr (floor h)))
  apply probability_mono
  intro A h
  let s := retained (history A) t.val
  let c := past (history A) (105+t.val)
  let w := (s.append c).winner
  have hw : w.snd ≠ 0 ∧ ‖w‖ ≤ r := by
    simpa [positiveCase,horizontalWinner,winLength,window,incoming,ChainState.reframe_winner,
      s,c,w] using h
  have hm := (s.append c).shortest.1
  rcases lt_or_gt_of_ne hw.1 with hn | hp
  · exact ⟨-w,(appendWindow _ _).neg_mem hm, by simpa using hn, by simpa using hw.2⟩
  · exact ⟨w,hm,hp,hw.2⟩

/-- The proved Blichfeldt constant gives an unconditional comparison along this path. -/
theorem retained_blichfeldt_floor (h : History) (i : ℕ) (hi : i ≤ 406) :
    exp (Blichfeldt.logFloor i) ≤ ZLattice.covolume (retained h i).M := by
  let P := path h
  suffices Blichfeldt.logFloor i ≤ log (P.det i) by
    exact (exp_le_exp.mpr this).trans_eq (exp_log (ZLattice.covolume_pos (retained h i).M _))
  induction i with
  | zero => rw [P.initial]; rfl
  | succ i ih =>
    let j : Fin 406 := ⟨i,by omega⟩
    have hp := ZLattice.covolume_pos (retained h i).M MeasureTheory.volume
    change 0 < P.det i at hp
    obtain ⟨v,hv,hv0,hq⟩ := P.modulus j
    have hs := P.shortest j
    have hs0 := norm_pos_iff.mpr hs.2.1
    have hmod := log_le_log hs0 ((hs.2.2 _ hv hv0).trans hq)
    let := P.discrete j
    let := P.lattice j
    have hc := HermiteWitness506.blichfeldt_shortest (P.window j) hs
    rw [← P.covol j] at hc
    have hlog := log_lt_log (pow_pos hs0 2) hc
    rw [log_pow,log_mul (by norm_num) (rpow_pos_of_pos hp _).ne',log_rpow hp] at hlog
    change 2*log ‖P.winner j‖ < log 61.45238 + _ * log (P.det i) at hlog
    change Blichfeldt.logFloor (i+1) ≤ log (P.det (j.val+1))
    rw [P.step,log_div hp.ne' hs0.ne',Blichfeldt.logFloor,max_le_iff]
    have ih' := ih (by omega)
    change Blichfeldt.logFloor i - _ ≤ log (P.det i) - _ ∧ _ ≤ log (P.det i) - _
    constructor <;> linarith

theorem positiveCase_blichfeldt (t : Fin 406) {r : ℝ} (hr : 0 < r) (hq : r < 3329) :
    probability (positiveCase r t.val) ≤ ballCharge 506 r (Blichfeldt.logFloor t.val) :=
  positiveCase_gaussian t hr hq (fun h ↦ retained_blichfeldt_floor h _ (by omega))

/-- Given the sharp physical Hermite estimate, the stronger envelope holds at
every prefix of the concrete path. -/
theorem retained_floor_of_hermite (h : History) (i : ℕ) (hi : i ≤ 406)
    (cap : ∀ j < i, winLength h j ^ 2 ≤ 56.2142 *
      ZLattice.covolume (retained h j).M ^ (2/(506:ℝ))) :
    exp (terminalLogFloor i) ≤ ZLattice.covolume (retained h i).M := by
  let P := path h
  suffices terminalLogFloor i ≤ log (P.det i) by
    exact (exp_le_exp.mpr this).trans_eq (exp_log (ZLattice.covolume_pos (retained h i).M _))
  induction i with
  | zero => rw [P.initial]; rfl
  | succ i ih =>
    let j : Fin 406 := ⟨i,by omega⟩
    obtain ⟨v,hv,hv0,hq⟩ := P.modulus j
    have hs := P.shortest j
    have hs0 := norm_pos_iff.mpr hs.2.1
    have hp : 0 < P.det i := ZLattice.covolume_pos (retained h i).M _
    have hmod := log_le_log hs0 ((hs.2.2 _ hv hv0).trans hq)
    have hc := cap i (by omega)
    change ‖P.winner j‖^2 ≤ 56.2142 * P.det i ^ _ at hc
    have hlog := log_le_log (pow_pos hs0 2) hc
    rw [log_pow, log_mul (by norm_num) (rpow_pos_of_pos hp _).ne', log_rpow hp] at hlog
    change terminalLogFloor (i+1) ≤ log (P.det (j.val+1))
    rw [P.step,log_div hp.ne' hs0.ne',terminalLogFloor,max_le_iff]
    have ih' := ih (by omega) (fun k hk ↦ cap k (by omega))
    change terminalLogFloor i - _ ≤ log (P.det i) - _ ∧ _ ≤ log (P.det i) - _
    constructor <;> linarith

/-- The period branch of the stronger recurrence suffices up through state 20. -/
theorem retained_floor_first20 (h : History) (i : ℕ) (hi : i ≤ 20) :
    exp (terminalLogFloor i) ≤ ZLattice.covolume (retained h i).M := by
  let P := path h
  have logq : 0 ≤ log 3329 := log_nonneg (by norm_num)
  have num : 125 * log 3329 ≤ 253 * log 56.2142 := by
    have hh := log_le_log (by positivity : 0 < (3329:ℝ)^125)
      (show (3329:ℝ)^125 ≤ (56.2142:ℝ)^253 by norm_num1)
    simpa only [log_pow,Nat.cast_ofNat] using hh
  suffices terminalLogFloor i = (400-i:ℝ)*log 3329 ∧ terminalLogFloor i ≤ log (P.det i) by
    exact (exp_le_exp.mpr this.2).trans_eq (exp_log (ZLattice.covolume_pos (retained h i).M _))
  induction i with
  | zero => rw [P.initial,terminalLogFloor,log_pow]; norm_num
  | succ i ih =>
    let j : Fin 406 := ⟨i,by omega⟩
    obtain ⟨e,hl⟩ := ih (by omega)
    obtain ⟨v,hv,hv0,hq⟩ := P.modulus j
    have hs := P.shortest j
    have hs0 := norm_pos_iff.mpr hs.2.1
    have hp : 0 < P.det i := ZLattice.covolume_pos (retained h i).M _
    have hmod := log_le_log hs0 ((hs.2.2 _ hv hv0).trans hq)
    have hi' : (i:ℝ) ≤ 19 := by exact_mod_cast (show i ≤ 19 by omega)
    have he : terminalLogFloor (i+1) = terminalLogFloor i-log 3329 := by
      rw [terminalLogFloor,max_eq_left]
      rw [e]
      nlinarith only [num,mul_nonneg (sub_nonneg.mpr hi') logq]
    rw [he,Nat.cast_succ]
    constructor
    · rw [e]; ring
    · change _ ≤ log (P.det (j.val+1))
      rw [P.step,log_div hp.ne' hs0.ne']
      change _ ≤ log (P.det i)-log ‖P.winner j‖
      linarith

theorem positiveCase_first21 (t : Fin 406) (ht : t.val ≤ 20)
    {r : ℝ} (hr : 0 < r) (hq : r < 3329) :
    probability (positiveCase r t.val) ≤ ballCharge 506 r (terminalLogFloor t.val) :=
  positiveCase_gaussian t hr hq (fun h ↦ retained_floor_first20 h _ ht)

end SigabaNeo.Wall1.ControlledPlane

#print axioms SigabaNeo.Wall1.ControlledPlane.candidateRatio_le_ballCharge
#print axioms SigabaNeo.Wall1.ControlledPlane.positiveCase_gaussian
#print axioms SigabaNeo.Wall1.ControlledPlane.retained_blichfeldt_floor
#print axioms SigabaNeo.Wall1.ControlledPlane.positiveCase_blichfeldt
#print axioms SigabaNeo.Wall1.ControlledPlane.retained_floor_of_hermite
#print axioms SigabaNeo.Wall1.ControlledPlane.positiveCase_first21
