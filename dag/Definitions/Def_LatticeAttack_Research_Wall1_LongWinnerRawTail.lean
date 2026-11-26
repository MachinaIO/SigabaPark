import Definitions.Def_LatticeAttack_Research_Wall1_LongWinnerRawMoments
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

set_option autoImplicit true

/-! From the unconditional physical-radius estimate in Part 222, equation (3),
to its crossing bound under the short conditional window (B). -/

noncomputable section
namespace SigabaNeo.Wall1.LongWinner.FourthMoment
open Real MeasureTheory Finset ControlledPlane TerminalProjection
open DualExit QaryMembership
open scoped Classical
local instance : Fact (Nat.Prime 3329) := ⟨by norm_num⟩

/-- Integration of an upper power tail of a finite random variable above one. -/
private lemma pareto_sum {Ω : Type*} [Fintype Ω] (Y : Ω → ℝ) (c : ℝ) (hc : 1 < c)
    (tail : ∀ t : ℝ, 1 < t → (∑ ω, if t < Y ω then (1:ℝ) else 0) ≤
      Fintype.card Ω * t ^ (-c)) :
    ∑ ω, Y ω ≤ Fintype.card Ω * (c / (c-1)) := by
  let f (ω : Ω) := (Set.Ioo 1 (Y ω)).indicator (fun _ ↦ (1:ℝ))
  have fi (ω : Ω) : IntegrableOn (f ω) (Set.Ioi 1) :=
    ((integrable_indicator_iff measurableSet_Ioo).2 (integrableOn_const
      (by simp [Real.volume_Ioo] : volume (Set.Ioo 1 (Y ω)) ≠ ⊤))).integrableOn
  have pt (ω : Ω) : Y ω ≤ 1 + ∫ t in Set.Ioi (1:ℝ), f ω t := by
    rw [show (∫ t in Set.Ioi (1:ℝ), f ω t) = max (Y ω - 1) 0 by
      dsimp only [f]
      rw [setIntegral_indicator measurableSet_Ioo, Set.inter_eq_right.mpr (show Set.Ioo 1 (Y ω) ⊆ Set.Ioi 1 from fun _ h ↦ h.1),
        setIntegral_const, smul_eq_mul,mul_one,volume_real_Ioo]]
    linarith only [le_max_left (Y ω-1) 0]
  have hint : (∫ t in Set.Ioi (1:ℝ), ∑ ω, f ω t) ≤
      ∫ t in Set.Ioi (1:ℝ), (Fintype.card Ω:ℝ)*t^(-c) := by
    apply setIntegral_mono_on (integrable_finsetSum univ fun ω _ ↦ fi ω)
      ((integrableOn_Ioi_rpow_of_lt (by linarith : -c < -1) zero_lt_one).const_mul _)
      measurableSet_Ioi
    intro t ht
    change 1 < t at ht
    simpa only [f,Set.indicator_apply, Set.mem_Ioo, ht, true_and] using tail t ht
  rw [integral_const_mul,integral_Ioi_rpow_of_lt (by linarith : -c < -1) zero_lt_one,
    one_rpow,integral_finsetSum _ (fun ω _ ↦ fi ω)] at hint
  calc
    _ ≤ _ := sum_le_sum (s:=univ) fun ω _ ↦ pt ω
    _ = _ := by rw [sum_add_distrib,sum_const,card_univ,nsmul_eq_mul,mul_one]
    _ ≤ _ := add_le_add le_rfl hint
    _ = _ := by rw [show -c+1 = -(c-1) by ring,neg_div_neg_eq]; field_simp; ring

private abbrev dimN (j : ℕ) := 506+j

/-- The raw graph void-probability input, with all previous columns averaged.
For small radii with RHS at least one this is the trivial probability bound. -/
def RawTailEstimate : Prop := ∀ j < 53, ∀ r : ℝ, 1690 ≤ r → r ≤ 3329 →
  probability (fun A ↦ r < s j A) ≤ 4*3329^400 / (rawVolume j * r^(dimN j))

private def vHigh (n : ℕ) : ℚ :=
  if n % 2 = 0 then (22/7)^(n/2) / (n/2).factorial
  else (22/7)^(n/2) * 2^(n/2+1) / n.doubleFactorial

private lemma small_radius (j : ℕ) (hj : j < 53) :
    rawVolume j * 1690^(dimN j) ≤ 4*3329^400 := by
  let n := dimN j
  let k := n/2
  have dim : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := by simp
  have : Nonempty (Fin n) := ⟨⟨0, by dsimp [n,dimN]; omega⟩⟩
  have hp : π ≤ 22/7 := by linarith only [Real.pi_lt_d4]
  have hvol : rawVolume j ≤ (vHigh n:ℝ) := by
    change volume.real (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) ≤ _
    unfold vHigh
    split_ifs with e
    · have h : n = 2*k := by dsimp [k]; omega
      rw [Measure.real, InnerProductSpace.volume_ball_of_dim_even (dim.trans h)]
      simp only [ENNReal.ofReal_one,one_pow,one_mul,ENNReal.toReal_ofReal (by positivity :
        0 ≤ π^k/(Nat.factorial k:ℝ))]
      push_cast
      gcongr
    · have h : n = 2*k+1 := by dsimp [k]; omega
      rw [Measure.real, InnerProductSpace.volume_ball_of_dim_odd (dim.trans h),dim]
      simp only [ENNReal.ofReal_one,one_pow,one_mul,ENNReal.toReal_ofReal (by positivity :
        0 ≤ π^k*2^(k+1)/(Nat.doubleFactorial n:ℝ))]
      push_cast
      gcongr
  have cert : ∀ i : Fin 53, vHigh (dimN i)*1690^(dimN i) ≤ 4*3329^400 := by decide +kernel
  have h := (Rat.cast_le (K := ℝ)).2 (cert ⟨j,hj⟩)
  push_cast only [Rat.cast_mul,Rat.cast_pow,Rat.cast_ofNat] at h
  exact (mul_le_mul_of_nonneg_right hvol (by positivity : 0 ≤ (1690:ℝ)^n)).trans h

theorem raw_moments_of_tail (raw : RawTailEstimate) : RawMomentEstimate := by
  intro j hj
  let n : ℕ := dimN j
  let d := log (4*3329^400/rawVolume j) / n
  let p := rawPower
  let y (A : Sample) := exp (p*(log (s j A)-d))
  have np : 0 < (n:ℝ) := by dsimp [n,dimN]; positivity
  have pp : 0 < p := by unfold p rawPower w; positivity
  have pl : p < n := by
    have hw : w 53 ≤ 1 := pow_le_one₀ (by norm_num : (0:ℝ) ≤ 505/506) (by norm_num)
    change 4*53*w 53 < ((506+j:ℕ):ℝ)
    push_cast
    linarith only [hw,Nat.cast_nonneg (α:=ℝ) j]
  have vpos : 0 < rawVolume j := by
    unfold rawVolume
    exact ENNReal.toReal_pos (Metric.measure_ball_pos volume _ zero_lt_one).ne' measure_ball_lt_top.ne
  have point (t : ℝ) (ht : 1 < t) :
      (∑ A : Sample, if t < y A then (1:ℝ) else 0) ≤ Fintype.card Sample*t^(-(n/p)) := by
    let r := exp (d + log t / p)
    have rt : 0 < r := exp_pos _
    have tp : 0 < t := by linarith
    have event (A : Sample) : t < y A ↔ r < s j A := by
      obtain ⟨hs,_,_,_⟩ := path_data (Restart506.path (history A)) j (by omega)
      change t < exp _ ↔ exp _ < _
      rw [← log_lt_log_iff tp (exp_pos _),log_exp,← log_lt_log_iff rt hs,log_exp]
      rw [← div_lt_iff₀' pp]
      constructor <;> intro h <;> linarith
    simp_rw [event]
    rw [← sum_filter,sum_const,nsmul_eq_mul,mul_one]
    by_cases hq : r ≤ 3329
    · have h : probability (fun A ↦ r < s j A) ≤ 4*3329^400 / (rawVolume j*r^n) := by
        by_cases lo : 1690 ≤ r
        · exact raw j hj r lo hq
        · apply le_trans (b := (1:ℝ)) _ ((le_div_iff₀ (mul_pos vpos (pow_pos rt _))).2 ?_)
          · unfold probability
            apply (div_le_iff₀ (by exact_mod_cast Fintype.card_pos)).2
            rw [one_mul]
            exact Nat.cast_le.mpr (Finset.card_le_univ _)
          · rw [one_mul]
            exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ rt.le (le_of_not_ge lo) n)
              vpos.le).trans (small_radius j hj)
      change ((univ.filter (fun A : Sample ↦ r < s j A)).card:ℝ) / Fintype.card Sample ≤ _ at h
      have eq : 4*3329^400 / (rawVolume j * r^n) = t ^ (-(n/p)) := by
        have a : (n:ℝ)*d = log (4*3329^400/rawVolume j) := by unfold d; field_simp
        rw [rpow_def_of_pos tp, ← div_div, ← exp_log (by positivity : 0 < 4*3329^400/rawVolume j),
          ← exp_nat_mul, ← exp_sub,← a]
        congr 1
        field_simp
        ring
      rw [eq] at h
      exact ((div_le_iff₀ (by exact_mod_cast Fintype.card_pos)).mp h).trans_eq (mul_comm ..)
    · have no (A : Sample) : ¬ r < s j A := by
        have h := (path_data (Restart506.path (history A)) j (by omega)).2.1
        exact not_lt_of_ge (h.trans (le_of_not_ge hq))
      simp only [no,filter_false,card_empty,Nat.cast_zero]
      positivity
  have mom := pareto_sum y (n/p) ((one_lt_div pp).2 pl) point
  have ratio : (n/p) / (n/p-1) = (n:ℝ)/(n-p) := by field_simp
  rw [ratio] at mom
  change (∑ A, exp (p*log (s j A))) ≤ _ * (exp (p*d)*_)
  have fact (A : Sample) : exp (p*log (s j A)) = exp (p*d)*y A := by
    unfold y; rw [← exp_add]; ring_nf
  simp_rw [fact,← mul_sum]
  exact (mul_le_mul_of_nonneg_left mom (exp_pos _).le).trans_eq (by ring)

/-- Under (B) on draws 54–405, equation (3) of Part 222 on draws 1–53
suffices on the original finite design law. -/
theorem crossing_of_raw_tail (raw : RawTailEstimate) (hc : Ceiling 53) :
    probability crosses < 2.4681 / (10:ℝ)^11 :=
  crossing_of_raw_moment_estimate (raw_moments_of_tail raw) hc

end SigabaNeo.Wall1.LongWinner.FourthMoment

#print axioms SigabaNeo.Wall1.LongWinner.FourthMoment.crossing_of_raw_tail
