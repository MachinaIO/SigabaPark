import Definitions.Def_LatticeAttack_Research_Wall1_HermiteSphereCertificate506

set_option autoImplicit true

/-! A count of long winners controls the incoming Gaussian-heuristic scale.
Path index zero is draw one. The first seven updates use the period witness. -/

noncomputable section
namespace SigabaNeo.Wall1.LongWinner
open Real TerminalProjection TerminalInterval Blichfeldt Finset
open scoped Classical

private abbrev a : ℝ := 505/506
private abbrev b : ℝ := 0.095311
private abbrev H : ℝ := 0.312981

lemma vol_pos : 0 < terminalBallVolume := by rw [terminalBallVolume_eq]; positivity

lemma volume_log : log terminalBallVolume / 506 ≤ -1.70161431262118 := by
  have upper := exp_upper (1.70161431262118/2) 2.341536074993667 (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
  push_cast at upper
  let p : ℚ := 3.141592653589794
  have hp : π ≤ (p : ℝ) := Real.pi_lt_d20.le.trans (by norm_num [p])
  have cert := (Rat.cast_le (K := ℝ)).2 (show (2.341536074993667 : ℚ)^1012 * p^253 ≤ (Nat.factorial 253)
    by decide +kernel)
  push_cast at cert
  have hc : exp (1.70161431262118 / 2) ^ 1012 * π^253 ≤ ((Nat.factorial 253) : ℝ) :=
    (mul_le_mul (pow_le_pow_left₀ (exp_pos _).le upper _) (pow_le_pow_left₀ pi_pos.le hp _)
      (by positivity) (by positivity)).trans cert
  have h : terminalBallVolume ≤ exp (-(506 * 1.70161431262118)) := by
    rw [terminalBallVolume_eq, exp_neg, le_inv_comm₀ (by positivity) (exp_pos _)]
    rw [show (506*1.70161431262118 : ℝ) = (1012:ℕ)*(1.70161431262118/2:ℝ) by norm_num, exp_nat_mul,
      inv_div, le_div_iff₀ (by positivity)]
    exact hc
  have := log_le_log vol_pos h
  rw [log_exp] at this
  linarith

lemma modulus_log : 8.110427237575 ≤ log 3329 := by
  have upper := exp_upper (8.110427237575/16) 1.6601396118373724 (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
  push_cast at upper
  apply (le_log_iff_exp_le (by norm_num)).2
  rw [show (8.110427237575:ℝ) = (16:ℕ)*(8.110427237575/16:ℝ) by norm_num, exp_nat_mul]
  exact (pow_le_pow_left₀ (exp_pos _).le upper 16).trans (by norm_num : (1.6601396118373724:ℝ)^16 ≤ 3329)

lemma rational_log_upper (x y : ℚ) (n : ℕ) (hn : n ≠ 0) (hx : 0 < x)
    (hy : 0 ≤ y/n) (hc : x ≤ (taylor (y/n) 20)^n) : log (x:ℝ) ≤ (y:ℝ) := by
  apply (log_le_iff_le_exp (by exact_mod_cast hx)).2
  have e : (y:ℝ) = (n:ℝ)*((y/n:ℚ):ℝ) := by push_cast; field_simp
  rw [e, exp_nat_mul]
  have h := exp_lower (y/n) _ hy le_rfl
  have hn0 : 0 ≤ taylor (y/n) 20 := by unfold taylor; positivity
  exact ((Rat.cast_le (K := ℝ)).2 hc).trans <| by
    rw [Rat.cast_pow]
    exact pow_le_pow_left₀ (by exact_mod_cast hn0) h _

private lemma cap_log : log 56.2142 / 2 + log terminalBallVolume / 506 ≤ H := by
  have h : log 56.2142 ≤ 4.02918 := by
    simpa using rational_log_upper 56.2142 4.02918 8 (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)
  linarith [volume_log]

private lemma ordinary_log : log 1.10 ≤ b := by
  simpa using rational_log_upper 1.10 0.095311 1 (by decide) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

lemma crossing_log : log 34.807 ≤ 3.549818515978 := by
  simpa using rational_log_upper 34.807 3.549818515978 4 (by decide) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

/-- Physical length of the winner on draw `i+1`, within the 406-window path. -/
def length (P : WindowPath) (i : ℕ) : ℝ := ‖P.winner ⟨min i 405, by omega⟩‖

/-- Exceptional draw, using its own incoming determinant. -/
def Long (P : WindowPath) (i : ℕ) : Prop := 1.10 * terminalScale (P.det i) < length P i

/-- Number of exceptional draws in the indicated prefix. -/
def longCount (P : WindowPath) (i : ℕ) := ((range i).filter (Long P)).card

private lemma count_succ (P : WindowPath) (i : ℕ) :
    longCount P (i+1) = longCount P i + if Long P i then 1 else 0 := by
  simp [longCount, range_add_one, filter_insert, apply_ite Finset.card, card_insert_of_notMem]
  split_ifs <;> simp

lemma log_scale {D : ℝ} (hD : 0 < D) :
    log (terminalScale D) = (log D - log terminalBallVolume)/506 := by
  rw [terminalScale, log_rpow (div_pos hD vol_pos), log_div hD.ne' vol_pos.ne']
  ring

attribute [local instance] WindowPath.lattice WindowPath.discrete

lemma path_data (P : WindowPath) (i : ℕ) (hi : i < 406) :
    0 < length P i ∧ length P i ≤ 3329 ∧ P.det (i+1) = P.det i / length P i ∧
      length P i ^ 2 ≤ 56.2142 * P.det i ^ (2/(506:ℝ)) := by
  let j : Fin 406 := ⟨i,hi⟩
  have e : length P i = ‖P.winner j‖ := by simp [length, min_eq_left (by omega : i ≤ 405), j]
  rw [e]
  obtain ⟨z,hz,h0,hq⟩ := P.modulus j
  have hs := P.shortest j
  refine ⟨norm_pos_iff.mpr hs.2.1, (hs.2.2 z hz h0).trans hq, P.step j, ?_⟩
  exact (P.covol j) ▸ HermiteWitness506.Sphere.shortest_cap (P.window j) hs

private def x (P : WindowPath) (i : ℕ) := log (terminalScale (P.det i))

lemma det_pos (P : WindowPath) (i : ℕ) (hi : i ≤ 406) : 0 < P.det i := by
  induction i with
  | zero => rw [P.initial]; positivity
  | succ i ih =>
    obtain ⟨hs,_,he,_⟩ := path_data P i (by omega)
    rw [he]; exact div_pos (ih (by omega)) hs

private lemma start_floor (P : WindowPath) : 8.00080 ≤ x P 7 := by
  have low (i : ℕ) (hi : i ≤ 7) : (400-(i:ℝ))*log 3329 ≤ log (P.det i) := by
    induction i with
    | zero => simp [P.initial, log_pow]
    | succ i ih =>
      obtain ⟨hs,hq,he,_⟩ := path_data P i (by omega)
      rw [he,log_div (det_pos P i (by omega)).ne' hs.ne']
      push_cast
      linarith [ih (by omega), log_le_log hs hq]
  rw [x, log_scale (det_pos P 7 (by decide))]
  have l := low 7 (by decide)
  norm_num only [Nat.cast_ofNat] at l
  linarith [volume_log,modulus_log]

private lemma step_floor (P : WindowPath) (i : ℕ) (hi : i < 405) :
    a*x P i - (if Long P i then H else b)/506 ≤ x P (i+1) := by
  obtain ⟨hs,_,he,hcap⟩ := path_data P i (by omega)
  have hD := det_pos P i (by omega)
  have hh := log_le_log (pow_pos hs 2) hcap
  rw [log_pow, log_mul (by norm_num) (rpow_pos_of_pos hD _).ne', log_rpow hD] at hh
  have l : x P (i+1) = x P i - log (length P i) / 506 := by
    unfold x
    rw [log_scale (det_pos P _ (by omega)), log_scale hD, he, log_div hD.ne' hs.ne']
    ring
  rw [l]
  split_ifs with h
  · rw [x, log_scale hD]; linarith only [hh,cap_log]
  · have hu := log_le_log hs (le_of_not_gt h)
    have hg : 0 < terminalScale (P.det i) := rpow_pos_of_pos (div_pos hD vol_pos) _
    rw [log_mul (by norm_num) hg.ne'] at hu
    change _ ≤ log 1.10 + x P i at hu
    linarith only [hu,ordinary_log]

/-- The sharp discounted penalty for `c` exceptions is attained when they come last. -/
private def lower (j c : ℕ) : ℝ :=
  a^j * (8.00080+b) - H + (H-b)*a^c

private lemma run_floor (P : WindowPath) (j : ℕ) (hj : 7+j ≤ 405) :
    lower j (longCount P (7+j)) ≤ x P (7+j) := by
  induction j with
  | zero =>
    have h : a^(longCount P 7) ≤ 1 := pow_le_one₀ (show 0 ≤ a by norm_num) (by norm_num : a ≤ 1)
    simp only [lower,pow_zero,one_mul,Nat.add_zero]
    linarith only [h, start_floor P]
  | succ j ih =>
    have h := mul_le_mul_of_nonneg_left (ih (by omega)) (by norm_num : 0 ≤ a)
    have step := step_floor P (7+j) (by omega)
    rw [show 7+(j+1) = (7+j)+1 by omega, count_succ]
    unfold lower at *
    split_ifs at step ⊢ with e
    · rw [pow_succ,pow_succ a (longCount P (7+j))]
      linarith only [step,h]
    · simp only [Nat.add_zero,pow_succ]
      have hc : a^(longCount P (7+j)) ≤ 1 := pow_le_one₀ (show 0 ≤ a by norm_num) (by norm_num : a ≤ 1)
      linarith only [step,h,hc]

/-- With at most 99 long winners among draws 1–405, every incoming GH scale
from draw 8 through draw 406 exceeds the crossing threshold. -/
theorem scale_of_at_most_99 (P : WindowPath) (hc : longCount P 405 ≤ 99)
    (i : ℕ) (lo : 7 ≤ i) (hi : i ≤ 405) : 34.807 < terminalScale (P.det i) := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le lo
  have hcount : longCount P (7+j) ≤ 99 :=
    (card_le_card (filter_subset_filter _ (range_mono hi))).trans hc
  have w := pow_le_pow_of_le_one (by norm_num : 0 ≤ a) (by norm_num : a ≤ 1) (by omega : j ≤ 398)
  have u := pow_le_pow_of_le_one (by norm_num : 0 ≤ a) (by norm_num : a ≤ 1) hcount
  have cert : (3.54982:ℚ) < (505/506)^398 * (8.00080+0.095311) - 0.312981 +
      (0.312981-0.095311)*(505/506)^99 := by decide +kernel
  have c := (Rat.cast_lt (K := ℝ)).2 cert
  push_cast at c
  have run := run_floor P j hi
  unfold lower at run
  apply lt_of_not_ge
  intro bad
  have pos := rpow_pos_of_pos (div_pos (det_pos P (7+j) (by omega)) vol_pos) (1/(506:ℝ))
  have hbad := log_le_log pos bad
  change x P (7+j) ≤ _ at hbad
  have lower_le : lower 398 99 ≤ lower j (longCount P (7+j)) := by
    unfold lower
    gcongr
  have good : 3.54982 < lower 398 99 := c
  exact (good.trans_le (lower_le.trans run)).not_ge (hbad.trans (crossing_log.trans (by norm_num)))

end SigabaNeo.Wall1.LongWinner

#print axioms SigabaNeo.Wall1.LongWinner.scale_of_at_most_99
