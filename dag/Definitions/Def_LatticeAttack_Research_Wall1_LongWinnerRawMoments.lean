import Definitions.Def_LatticeAttack_Research_Wall1_LongWinnerFourthMoment

set_option autoImplicit true

/-! Part 222's short fourth-moment window with the raw marginal estimate (5).
Rational enclosures below use the even/odd formulas for the Euclidean ball. -/

noncomputable section
namespace SigabaNeo.Wall1.LongWinner.FourthMoment
open Real Finset ControlledPlane TerminalProjection TerminalInterval MeasureTheory Metric
open DualExit QaryMembership
open scoped Classical
local instance : Fact (Nat.Prime 3329) := ⟨by norm_num⟩

abbrev rawPower : ℝ := 4*53*w 53
private abbrev N (j : ℕ) := 506+j

/-- Actual Euclidean volume in the unprojected dimension at zero-based draw `j`. -/
def rawVolume (j : ℕ) : ℝ := volume.real (ball (0 : EuclideanSpace ℝ (Fin (N j))) 1)

/-- Part 222, (5), after dropping the period branch (supplied by the physical path).
Here `exp (p log T)` is `T^p` for `T=(4q^400/V_N)^(1/N)`. -/
def RawMomentEstimate : Prop := ∀ j < 53,
  (∑ A : Sample, exp (rawPower * log (s j A))) ≤
    (Fintype.card Sample:ℝ) * (exp (rawPower * (log (4*3329^400/rawVolume j)/N j)) *
      (N j / ((N j:ℝ)-rawPower)))

private def vLow (n : ℕ) : ℚ :=
  let k := n/2
  if n % 2 = 0 then 3.14159265358979^k / k.factorial
  else 3.14159265358979^k * 2^(k+1) / n.doubleFactorial

private lemma volume_lower (j : ℕ) : (vLow (N j) : ℝ) ≤ rawVolume j := by
  let n := N j
  let k := n/2
  have dim : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := by simp
  have hp : (3.14159265358979 : ℝ) ≤ π := (by norm_num : (3.14159265358979:ℝ) ≤
    3.14159265358979323846).trans Real.pi_gt_d20.le
  have : Nonempty (Fin n) := ⟨⟨0, by dsimp [n,N]; omega⟩⟩
  change (vLow n : ℝ) ≤ volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1)
  unfold vLow
  split_ifs with e
  · have h : n = 2*k := by dsimp [k]; omega
    rw [Measure.real, InnerProductSpace.volume_ball_of_dim_even (dim.trans h)]
    simp only [ENNReal.ofReal_one,one_pow,one_mul,ENNReal.toReal_ofReal (by positivity :
      0 ≤ π^k/(Nat.factorial k:ℝ))]
    push_cast
    exact div_le_div_of_nonneg_right (pow_le_pow_left₀ (by norm_num) hp _) (by positivity)
  · have h : n = 2*k+1 := by dsimp [k]; omega
    rw [Measure.real,InnerProductSpace.volume_ball_of_dim_odd (dim.trans h),dim]
    simp only [ENNReal.ofReal_one,one_pow,one_mul,ENNReal.toReal_ofReal (by positivity :
      0 ≤ π^k*2^(k+1)/(Nat.doubleFactorial n:ℝ))]
    push_cast
    gcongr

-- Certified upper bounds for T, log T, and the log marginal moment radius.
private def radius (j : ℕ) : ℚ :=
  ((#[33467966909041, 33079453250030, 32697016061725, 32320539411666, 31949909947737,
      31585016832968, 31225751682173, 30872008500361, 30523683622877, 30180675657216,
      29842885426445, 29510215914211, 29182572211260, 28859861463432, 28541992821097,
      28228877389967, 27920428183261, 27616560075172, 27317189755603, 27022235686129,
      26731618057153, 26445258746212, 26163081277416, 25885010781964, 25610973959722,
      25340899041827, 25074715754286, 24812355282536, 24553750236951, 24298834619250,
      24047543789795, 23799814435746, 23555584540050, 23314793351236, 23077381354004,
      22843290240569, 22612462882754, 22384843304798, 22160376656869, 21939009189255,
      21720688227216, 21505362146480, 21292980349362, 21083493241488, 20876852209115,
      20673009597019, 20471918686942, 20273533676578, 20077809659094, 19884702603155,
      19694169333449, 19506167511700, 19320655618153] : Array ℕ)[j]! : ℚ) / 10^10

private def logRadius (j : ℕ) : ℚ :=
  ((#[81157589557, 81040825279, 80924540078, 80808731093, 80693395483,
      80578530433, 80464133148, 80350200856, 80236730805, 80123720267,
      80011166533, 79899066916, 79787418751, 79676219391, 79565466212,
      79455156610, 79345287999, 79235857816, 79126863515, 79018302570,
      78910172477, 78802470748, 78695194915, 78588342529, 78481911160,
      78375898395, 78270301840, 78165119120, 78060347878, 77955985772,
      77852030481, 77748479699, 77645331138, 77542582529, 77440231617,
      77338276165, 77236713953, 77135542777, 77034760449, 76934364798,
      76834353669, 76734724922, 76635476434, 76536606095, 76438111814,
      76339991513, 76242243130, 76144864617, 76047853942, 75951209087,
      75854928051, 75759008843, 75663449489] : Array ℕ)[j]! : ℚ) / 10^10

private def momentRadius (j : ℕ) : ℚ :=
  ((#[81104272376, 81062943643, 80946609406, 80830751603, 80715367392,
      80600453955, 80486008498, 80372028245, 80258510444, 80145452365,
      80032851299, 79920704556, 79809009470, 79697763394, 79586963701,
      79476607786, 79366693062, 79257216965, 79148176947, 79039570481,
      78931395062, 78823648201, 78716327428, 78609430293, 78502954365,
      78396897230, 78291256492, 78186029776, 78081214723, 77976808989,
      77872810253, 77769216208, 77666024565, 77563233053, 77460839416,
      77358841416, 77257236832, 77156023459, 77055199108, 76954761607,
      76854708799, 76755038544, 76655748718, 76556837209, 76458301926,
      76360140789, 76262351736, 76164932717, 76067881699, 75971196665,
      75874875610, 75778916544, 75683317492] : Array ℕ)[j]! : ℚ) / 10^10

private abbrev pLo : ℚ := 105.66204968384
private abbrev pHi : ℚ := 105.66204968385

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem certificates : ∀ j : Fin 53,
    0 < vLow (N j) ∧ 0 < radius j ∧
    4*3329^400 ≤ vLow (N j) * radius j ^ N j ∧
    0 ≤ logRadius j / 16 ∧ radius j ≤ taylor (logRadius j / 16) 20 ^ 16 ∧
    (8.110427237576 ≤ momentRadius j ∨
      (0 ≤ momentRadius j - logRadius j ∧
        (N j : ℚ) / (N j-pHi) ≤ taylor (pLo*(momentRadius j-logRadius j)) 20)) := by
  decide +kernel

private lemma power_range : (pLo:ℝ) ≤ rawPower ∧ rawPower ≤ (pHi:ℝ) := by
  have q : pLo ≤ 212*(505/506:ℚ)^352 ∧ 212*(505/506:ℚ)^352 ≤ pHi := by decide +kernel
  obtain ⟨h,k⟩ := q
  change (pLo:ℝ) ≤ 4*53*(505/506:ℝ)^352 ∧ 4*53*(505/506:ℝ)^352 ≤ (pHi:ℝ)
  rw [show (4:ℝ)*53 = 212 by norm_num]
  constructor
  · simpa only [Rat.cast_mul, Rat.cast_ofNat, Rat.cast_div, Rat.cast_pow] using
      (Rat.cast_le (K := ℝ)).2 h
  · simpa only [Rat.cast_mul, Rat.cast_ofNat, Rat.cast_div, Rat.cast_pow] using
      (Rat.cast_le (K := ℝ)).2 k


private theorem prefix_of_raw (raw : RawMomentEstimate) :
    PrefixMoments 53 (fun j ↦ (momentRadius j : ℝ)) := by
  intro j hj
  obtain ⟨hv,hr,hvol,hlog,ht,hn⟩ := certificates ⟨j,hj⟩
  have hP : 0 < rawPower := lt_of_lt_of_le (by norm_num [pLo]) power_range.1
  have npos : (0 : ℝ) < N j := by dsimp [N]; positivity
  have nlarge : (pHi:ℝ) < N j := by push_cast [pHi,N]; linarith only [Nat.cast_nonneg (α := ℝ) j]
  let d : ℝ := logRadius j
  let L : ℝ := momentRadius j
  have hs (A : Sample) := (path_data (Restart506.path (history A)) j (by omega)).1
  change ∑ A : Sample, exp (rawPower * (log (s j A) - L)) ≤ _
  rcases hn with early | late
  · have logq : log 3329 ≤ (8.110427237576:ℝ) := by
      simpa using rational_log_upper 3329 8.110427237576 16 (by decide) (by decide +kernel)
        (by decide +kernel) (by decide +kernel)
    have ll : 8.110427237576 ≤ L := by simpa only [Rat.cast_ofScientific] using (Rat.cast_le (K := ℝ)).2 early
    have point (A : Sample) : exp (rawPower*(log (s j A)-L)) ≤ 1 := by
      apply exp_le_one_iff.mpr
      exact mul_nonpos_of_nonneg_of_nonpos hP.le (sub_nonpos.mpr
        ((log_le_log (hs A) (path_data _ _ (by omega)).2.1).trans (logq.trans ll)))
    simpa only [sum_const,card_univ,nsmul_eq_mul,mul_one] using sum_le_sum (s:=univ) (fun A _ ↦ point A)
  · have vd := volume_lower j
    have vp : 0 < rawVolume j := lt_of_lt_of_le (by exact_mod_cast hv) vd
    have rp : 0 < (radius j:ℝ) := by exact_mod_cast hr
    have hvol' : (4:ℝ)*3329^400 ≤ (vLow (N j):ℝ)*(radius j:ℝ)^(N j) := by exact_mod_cast hvol
    have gr : (4:ℝ)*3329^400 / rawVolume j ≤ (radius j:ℝ)^(N j) :=
      (div_le_iff₀ vp).2 ((hvol'.trans (mul_le_mul_of_nonneg_right vd (pow_pos rp _).le)).trans_eq (mul_comm ..))
    have lg := log_le_log (by positivity) gr
    rw [log_pow] at lg
    have ld : log (4*3329^400/rawVolume j)/N j ≤ d :=
      (div_le_iff₀ npos).2 (lg.trans ((mul_le_mul_of_nonneg_left
        (rational_log_upper _ _ 16 (by decide) hr hlog ht) npos.le).trans_eq (mul_comm ..)))
    have delta : 0 ≤ L-d := by simpa only [Rat.cast_zero,Rat.cast_sub] using (Rat.cast_le (K := ℝ)).2 late.1
    have lower := exp_lower (pLo*(momentRadius j-logRadius j)) ((N j : ℚ)/(N j-pHi))
      (mul_nonneg (by decide +kernel) late.1) late.2
    push_cast only [Rat.cast_div,Rat.cast_natCast,Rat.cast_sub,Rat.cast_mul] at lower
    have corr : (N j:ℝ)/(N j-rawPower) ≤ exp (rawPower*(L-d)) :=
      (div_le_div_of_nonneg_left npos.le (sub_pos.mpr nlarge)
        (sub_le_sub_left power_range.2 _)).trans (lower.trans
          (exp_le_exp.mpr (mul_le_mul_of_nonneg_right power_range.1 delta)))
    have bound : exp (rawPower*(log (4*3329^400/rawVolume j)/N j)) *
        (N j / ((N j:ℝ)-rawPower)) ≤ exp (rawPower*L) := by
      calc
        _ ≤ exp (rawPower*d) * exp (rawPower*(L-d)) :=
          mul_le_mul (exp_le_exp.mpr (mul_le_mul_of_nonneg_left ld hP.le)) corr
            (div_nonneg npos.le (sub_nonneg.mpr (power_range.2.trans nlarge.le))) (exp_pos _).le
        _ = _ := by rw [← exp_add]; ring_nf
    have r := (raw j hj).trans (mul_le_mul_of_nonneg_left bound (by positivity))
    simp_rw [mul_sub,exp_sub]
    rw [← sum_div]
    exact (div_le_iff₀ (exp_pos _)).2 r

/-- Short-window result under the Part 222 raw marginal estimate (5) and the
conditional fourth-moment ceiling on draws 54–405. -/
theorem crossing_of_raw_moment_estimate (raw : RawMomentEstimate) (hc : Ceiling 53) :
    probability crosses < 2.4681 / (10:ℝ)^11 := by
  apply crossing_of_short_fourth_moment hc _ (prefix_of_raw raw)
  have h : ∑ j ∈ range 53, momentRadius j ≤ 53*7.833834628 := by decide +kernel
  simpa only [Rat.cast_sum,Rat.cast_mul,Rat.cast_ofNat,Rat.cast_ofScientific] using (Rat.cast_le (K := ℝ)).2 h

end SigabaNeo.Wall1.LongWinner.FourthMoment

#print axioms SigabaNeo.Wall1.LongWinner.FourthMoment.crossing_of_raw_moment_estimate
