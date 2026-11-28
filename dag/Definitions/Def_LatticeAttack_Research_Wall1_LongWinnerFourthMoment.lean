import Definitions.Def_LatticeAttack_Research_Wall1_LongWinnerProbability
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

set_option autoImplicit true

/-! Conditional fourth moments and the probability of a first crossing.
The estimate starts at a freely chosen prefix and exposes the law required there. -/

noncomputable section
namespace SigabaNeo.Wall1.LongWinner.FourthMoment
open Real Finset ControlledPlane TerminalProjection TerminalProjection.Restart506
open DualExit QaryMembership
open scoped Classical
local instance : Fact (Nat.Prime 3329) := ⟨by norm_num⟩

private abbrev a : ℝ := 505/506
private abbrev M : ℝ := 1.786
private abbrev X : ℝ := log 34.807
private abbrev P (A : Sample) := path (history A)
/-- Physical winner length at zero-based draw index. -/
abbrev s (i : ℕ) (A : Sample) := length (P A) i
private def x (i : ℕ) (A : Sample) := log (terminalScale ((P A).det i))
/-- Discount from a given determinant index to the final index 405. -/
def w (i : ℕ) : ℝ := a^(405-i)

/-- Tests measurable from the winner lengths already revealed at entry. -/
def Predictable (i : ℕ) (f : Sample → ℝ) : Prop :=
  ∀ A B, (∀ j < i, s j A = s j B) → f A = f B

/-- Conditional fourth-moment bound (B) on draws `m+1,…,405`.
Testing against nonnegative past payoffs avoids conditioning on null atoms. -/
def Ceiling (m : ℕ) : Prop :=
  ∀ i, m ≤ i → i < 405 → ∀ f : Sample → ℝ, Predictable i f → (∀ A, 0 ≤ f A) →
    (∑ A, f A * (s i A / terminalScale ((P A).det i))^4) ≤ M * ∑ A, f A

private lemma update (i : ℕ) (hi : i < 405) (A : Sample) :
    x (i+1) A = x i A - log (s i A) / 506 := by
  obtain ⟨hs,_,he,_⟩ := path_data (P A) i (by omega)
  unfold x
  rw [log_scale (det_pos _ _ (by omega)), log_scale (det_pos _ _ (by omega)),he,
    log_div (det_pos _ _ (by omega)).ne' hs.ne']
  ring

private lemma x_predictable (i : ℕ) (hi : i ≤ 405) : Predictable i (x i) := by
  intro A B he
  induction i with
  | zero => simp [x, Blichfeldt.WindowPath.initial]
  | succ i ih =>
    rw [update _ (by omega), update _ (by omega), he i (by omega),
      ih (by omega) (fun j hj ↦ he j (by omega))]

private def paid (i : ℕ) (A : Sample) := ∃ j ∈ Icc 395 i, x j A < X

def potential (i : ℕ) (A : Sample) :=
  exp (2024 * (X - w i * x i A) + 506 * (1-w i) * log M)

private def stopped (i : ℕ) (A : Sample) := if paid i A then 1 else potential i A

private lemma w_le (i : ℕ) : w i ≤ 1 :=
  pow_le_one₀ (by norm_num : 0 ≤ a) (by norm_num : a ≤ 1)

private lemma w_pos (i : ℕ) : 0 < w i := pow_pos (by norm_num : 0 < a) _

private lemma crossing_value {i : ℕ} {A : Sample} (h : x i A < X) : 1 ≤ potential i A := by
  have hx : 0 < X := log_pos (by norm_num)
  have hM : 0 ≤ log M := log_nonneg (by norm_num)
  apply one_le_exp_iff.mpr
  have hw := (mul_le_mul_of_nonneg_left h.le (w_pos i).le).trans
    (mul_le_of_le_one_left hx.le (w_le i))
  exact add_nonneg (by linarith) (mul_nonneg (by linarith [w_le i]) hM)

private lemma potential_step (i : ℕ) (hi : i < 405) (A : Sample) :
    potential (i+1) A ≤ potential i A *
      ((1-w (i+1)) + w (i+1) * (s i A / terminalScale ((P A).det i))^4 / M) := by
  have hw : w i = a*w (i+1) := by
    unfold w
    rw [show 405-i = 405-(i+1)+1 by omega,pow_succ,mul_comm]
  let y := 4*(log (s i A) - x i A)-log M
  have equality : potential (i+1) A = potential i A * exp (w (i+1)*y) := by
    unfold potential
    rw [← exp_add,update i hi, hw]
    congr 1
    dsimp [y]
    ring
  have cv := convexOn_exp.2 (Set.mem_univ (0:ℝ)) (Set.mem_univ y)
    (sub_nonneg.mpr (w_le (i+1))) (w_pos (i+1)).le (sub_add_cancel 1 (w (i+1)))
  simp only [smul_eq_mul,mul_zero,zero_add,exp_zero,mul_one] at cv
  have hs := (path_data (P A) i (by omega)).1
  have hg : 0 < terminalScale ((P A).det i) :=
    rpow_pos_of_pos (div_pos (det_pos _ _ (by omega)) vol_pos) _
  have ey : exp y = (s i A / terminalScale ((P A).det i))^4 / M := by
    change exp ((4:ℕ)*(log (s i A)-log (terminalScale ((P A).det i))) - log M) = _
    rw [exp_sub,exp_nat_mul,exp_sub,exp_log hs,exp_log hg,exp_log (by norm_num : 0 < M)]
  rw [equality]
  apply mul_le_mul_of_nonneg_left _ (exp_pos _).le
  simpa only [ey,mul_div_assoc] using cv

private lemma sum_step {m i : ℕ} (hc : Ceiling m) (hm : m ≤ i) (hi : i < 405) :
    ∑ A, stopped (i+1) A ≤ ∑ A, stopped i A := by
  let f (A : Sample) := if paid i A then 0 else potential i A
  have fp : Predictable i f := by
    intro A B he
    have hx (j : ℕ) (hj : j ≤ i) := x_predictable j (by omega) A B (fun k hk ↦ he k (by omega))
    have hp : paid i A ↔ paid i B := by
      unfold paid
      exact exists_congr fun j ↦ and_congr_right fun hj ↦ by rw [hx j (mem_Icc.mp hj).2]
    simp only [f, hp, potential, hx i le_rfl]
  have fn (A : Sample) : 0 ≤ f A := by unfold f; split_ifs <;> simp [potential, (exp_pos _).le]
  have H := hc i hm hi f fp fn
  let c (A : Sample) := if paid i A then (1:ℝ) else 0
  let r (A : Sample) := (s i A / terminalScale ((P A).det i))^4
  have point (A : Sample) : stopped (i+1) A ≤ c A +
      (1-w (i+1))*f A + (w (i+1)/M)*(f A*r A) := by
    by_cases old : paid i A
    · obtain ⟨j,hj,hb⟩ := id old
      have next : paid (i+1) A := ⟨j,mem_Icc.mpr ⟨(mem_Icc.mp hj).1, by
        have := (mem_Icc.mp hj).2; omega⟩,hb⟩
      simp [stopped,c,f,old,next]
    · have bound : stopped (i+1) A ≤ potential (i+1) A := by
        unfold stopped
        split_ifs with next
        · obtain ⟨j,hj,hb⟩ := next
          have e : j = i+1 := by
            by_contra hn
            exact old ⟨j,mem_Icc.mpr ⟨(mem_Icc.mp hj).1,by have := (mem_Icc.mp hj).2; omega⟩,hb⟩
          exact crossing_value (e ▸ hb)
        · exact le_rfl
      simp only [c,f,old,ite_false,zero_add]
      exact (bound.trans (potential_step i hi A)).trans_eq (by unfold r; ring)
  have total (A : Sample) : stopped i A = c A + f A := by
    by_cases h : paid i A <;> simp [stopped,c,f,h]
  calc
    _ ≤ _ := sum_le_sum fun A _ ↦ point A
    _ = (∑ A, c A) + (1-w (i+1))*(∑ A, f A) +
        (w (i+1)/M)*(∑ A, f A*r A) := by simp only [sum_add_distrib,mul_sum]
    _ ≤ (∑ A, c A) + (1-w (i+1))*(∑ A, f A) +
        (w (i+1)/M)*(M*∑ A, f A) := add_le_add le_rfl (mul_le_mul_of_nonneg_left H (div_nonneg (w_pos (i+1)).le (by norm_num : 0 ≤ M)))
    _ = ∑ A, stopped i A := by simp_rw [total,sum_add_distrib]; ring

/-- The initial-law input in the stopped fourth-moment comparison. -/
theorem crossing_from_prefix {m : ℕ} (hm : m < 395) (hc : Ceiling m) :
    probability crosses ≤ (∑ A, potential m A) / Fintype.card Sample := by
  have decrease (j : ℕ) (hj : m ≤ j) (ht : j ≤ 405) :
      ∑ A, stopped j A ≤ ∑ A, stopped m A := by
    induction j, hj using Nat.le_induction with
    | base => rfl
    | succ j hj ih => exact (sum_step hc hj (by omega)).trans (ih (by omega))
  have start (A : Sample) : stopped m A = potential m A := by
    have empty : ¬paid m A := by rintro ⟨j,hj,_⟩; have := mem_Icc.mp hj; omega
    simp [stopped,empty]
  have endp (A : Sample) : (if crosses A then (1:ℝ) else 0) ≤ stopped 405 A := by
    split_ifs with hit
    · obtain ⟨j,hj,hg⟩ := hit
      have h : paid 405 A := ⟨j,hj,log_lt_log (rpow_pos_of_pos
        (div_pos (det_pos _ _ (by have := (mem_Icc.mp hj).2; omega)) vol_pos) _) hg⟩
      simp [stopped,h]
    · unfold stopped; split_ifs <;> simp [potential, (exp_pos _).le]
  unfold probability designs
  apply div_le_div_of_nonneg_right _ (by positivity)
  have sumend := (sum_le_sum (s := univ) (fun A _ ↦ endp A)).trans (decrease 405 (by omega) le_rfl)
  simpa only [← sum_filter,sum_const, nsmul_eq_mul,mul_one,start] using sumend


private lemma initial_lower (A : Sample) :
    400*8.110427237575/506 + 1.70161431262118 ≤ x 0 A := by
  rw [x, log_scale (det_pos _ _ (by decide)), Blichfeldt.WindowPath.initial, log_pow]
  push_cast
  linarith only [volume_log,modulus_log]

private lemma prefix_log (i : ℕ) (hi : i ≤ 405) (A : Sample) :
    x i A = x 0 A - (∑ j ∈ range i, log (s j A))/506 := by
  induction i with
  | zero => simp
  | succ i ih => rw [update _ (by omega), ih (by omega), sum_range_succ]; ring

/-- Marginal moment estimates for the prefix. They are unconditional, so they can
be applied even when the first `m` lengths are dependent. -/
def PrefixMoments (m : ℕ) (L : ℕ → ℝ) : Prop :=
  ∀ j < m, (∑ A : Sample, exp (4*m*w m*(log (s j A)-L j))) ≤ Fintype.card Sample

private def logBound (m : ℕ) (L : ℕ → ℝ) : ℝ :=
  2024 * (3.549818515978 - w m * (400*8.110427237575/506 + 1.70161431262118)) +
    506*(1-w m)*0.579978482455 + 4*w m*(∑ j ∈ range m, L j)

/-- Finite Jensen/Hölder estimate for the initial potential, followed by the
stopped conditional estimate for the remaining draws. -/
theorem crossing_from_marginals {m : ℕ} (hm : 0 < m) (hm' : m < 395) (L : ℕ → ℝ)
    (raw : PrefixMoments m L) (hc : Ceiling m) : probability crosses ≤ exp (logBound m L) := by
  have mr : (m:ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  let z (j : ℕ) (A : Sample) := 4*m*w m*(log (s j A)-L j)
  have jensen (A : Sample) : exp (4*w m*(∑ j ∈ range m, (log (s j A)-L j))) ≤
      (m:ℝ)⁻¹ * ∑ j ∈ range m, exp (z j A) := by
    have h := convexOn_exp.map_sum_le (t := range m) (w := fun _ : ℕ ↦ (m:ℝ)⁻¹)
      (p := fun j ↦ z j A) (fun _ _ ↦ by positivity)
      (by simp only [sum_const,card_range,nsmul_eq_mul,mul_inv_cancel₀ mr])
      (fun _ _ ↦ Set.mem_univ _)
    simp only [smul_eq_mul, ← mul_sum] at h
    convert h using 2
    dsimp [z]
    rw [← mul_sum]
    field_simp
  have ml : log M ≤ 0.579978482455 := by
    simpa using rational_log_upper 1.786 0.579978482455 2 (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)
  have point (A : Sample) : potential m A ≤
      (exp (logBound m L) * (m:ℝ)⁻¹) * ∑ j ∈ range m, exp (z j A) := by
    rw [mul_assoc]
    apply le_trans _ (mul_le_mul_of_nonneg_left (jensen A) (exp_pos _).le)
    rw [← exp_add]
    apply exp_le_exp.mpr
    rw [prefix_log m (by omega), sum_sub_distrib]
    unfold logBound
    have h1 := mul_le_mul_of_nonneg_left (initial_lower A) (w_pos m).le
    have h2 := mul_le_mul_of_nonneg_left ml (sub_nonneg.mpr (w_le m))
    dsimp only [X]
    linear_combination 2024*crossing_log + 2024*h1 + 506*h2
  have bound : (∑ A : Sample, ∑ j ∈ range m, exp (z j A)) ≤ (m:ℝ)*Fintype.card Sample := by
    rw [sum_comm]
    calc
      _ ≤ ∑ _ ∈ range m, (Fintype.card Sample : ℝ) := sum_le_sum fun j hj ↦ raw j (mem_range.mp hj)
      _ = _ := by simp only [sum_const,card_range,nsmul_eq_mul]
  apply (crossing_from_prefix hm' hc).trans
  apply (div_le_iff₀ (by exact_mod_cast Fintype.card_pos)).2
  calc
    _ ≤ _ := sum_le_sum fun A _ ↦ point A
    _ = _ := (mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left bound (mul_nonneg (exp_pos _).le (by positivity))
    _ = _ := by field_simp

private def ratBound (m : ℕ) (avg : ℚ) : ℚ :=
  let w := (505/506 : ℚ)^(405-m)
  2024 * (3.549818515978 - w * (400*8.110427237575/506 + 1.70161431262118)) +
    506*(1-w)*0.579978482455 + 4*w*(m*avg)

private lemma logBound_le {m : ℕ} {L : ℕ → ℝ} {avg : ℚ}
    (hl : ∑ j ∈ range m, L j ≤ m*(avg:ℝ)) : logBound m L ≤ (ratBound m avg : ℝ) := by
  unfold logBound ratBound
  push_cast
  apply add_le_add le_rfl
  exact mul_le_mul_of_nonneg_left hl (by linarith [w_pos m])

private lemma exp_neg_bound (k c : ℚ) (hk : 0 ≤ k) (hc : 0 < c)
    (cert : 1/c < (TerminalInterval.taylor (k/32) 20)^32) : exp (-(k:ℝ)) < (c:ℝ) := by
  rw [exp_neg, inv_lt_comm₀ (exp_pos _) (by exact_mod_cast hc)]
  have h := TerminalInterval.exp_lower (k/32) _ (by positivity) le_rfl
  have hz : 0 ≤ TerminalInterval.taylor (k/32) 20 := by unfold TerminalInterval.taylor; positivity
  rw [show (k:ℝ) = (32:ℕ)*((k/32:ℚ):ℝ) by push_cast; ring,exp_nat_mul]
  have e := (Rat.cast_lt (K := ℝ)).2 cert
  push_cast at e
  apply lt_of_lt_of_le _ (pow_le_pow_left₀ (by exact_mod_cast hz) h 32)
  simpa only [one_div] using e

/-- Part 220, under (B) on draws 11–405 only. The first ten use the period
witness, so the probability statement needs no raw-graph moment premise. -/
theorem crossing_of_fourth_moment (hc : Ceiling 10) :
    probability crosses < 2.69977 / (10:ℝ)^11 := by
  let L := fun _ : ℕ ↦ (8.110427237576 : ℝ)
  have qlog : log 3329 ≤ 8.110427237576 := by
    simpa using rational_log_upper 3329 8.110427237576 16 (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)
  have raw : PrefixMoments 10 L := by
    intro j hj
    have h (A : Sample) : exp (4*10*w 10*(log (s j A)-L j)) ≤ 1 := by
      obtain ⟨hs,hq,_,_⟩ := path_data (P A) j (by omega)
      apply exp_le_one_iff.mpr
      exact mul_nonpos_of_nonneg_of_nonpos (by linarith [w_pos 10])
        (sub_nonpos.mpr ((log_le_log hs hq).trans qlog))
    simpa only [Nat.cast_ofNat,sum_const, card_univ,nsmul_eq_mul,mul_one] using
      (sum_le_sum (s := univ) (fun A _ ↦ h A))
  have numeric : ratBound 10 8.110427237576 ≤ -24.3352707 := by decide +kernel
  have h := logBound_le (m := 10) (L := L) (avg := 8.110427237576) (by simp [L])
  have hr := (Rat.cast_le (K := ℝ)).2 numeric
  have he := (crossing_from_marginals (by decide) (by decide) L raw hc).trans
    (exp_le_exp.mpr (h.trans hr))
  apply he.trans_lt
  convert exp_neg_bound 24.3352707 (2.69977/10^11) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) using 1 <;> push_cast <;> ring

/-- Part 222, row (B), with separate marginal estimates from the raw graph on
draws 1–53 and the conditional fourth moment on draws 54–405. The prefix mean
is the logarithm of the geometric mean of the marginal moment radii. -/
theorem crossing_of_short_fourth_moment (hc : Ceiling 53) (L : ℕ → ℝ)
    (raw : PrefixMoments 53 L) (hradius : ∑ j ∈ range 53, L j ≤ 53*7.833834628) :
    probability crosses < 2.4681 / (10:ℝ)^11 := by
  have numeric : ratBound 53 7.833834628 ≤ -24.4249921 := by decide +kernel
  have h := logBound_le (m := 53) (L := L) (avg := 7.833834628) (by simpa using hradius)
  have he := (crossing_from_marginals (by decide) (by decide) L raw hc).trans
    (exp_le_exp.mpr (h.trans ((Rat.cast_le (K := ℝ)).2 numeric)))
  apply he.trans_lt
  convert exp_neg_bound 24.4249921 (2.4681/10^11) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) using 1 <;> push_cast <;> ring

end SigabaNeo.Wall1.LongWinner.FourthMoment

#print axioms SigabaNeo.Wall1.LongWinner.FourthMoment.crossing_of_fourth_moment
#print axioms SigabaNeo.Wall1.LongWinner.FourthMoment.crossing_of_short_fourth_moment
