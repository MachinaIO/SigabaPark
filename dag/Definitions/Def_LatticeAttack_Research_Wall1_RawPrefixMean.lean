import Definitions.Def_LatticeAttack_Research_Wall1_CharlierVoidKernel

set_option autoImplicit true

/-! # Exact first moment of the fixed raw candidate family

Every fixed candidate has exactly one raw syndrome for every matrix. Hence
the mean over labels is exactly the candidate cardinality divided by the
label cardinality, even before averaging over matrices. No independence
between candidates, selected histories, or matrix entries is used.
-/

noncomputable section
namespace SigabaNeo.Wall1.RawPrefixOccupancy
open Finset ControlledPlane TerminalProjection FactorialMomentTransfer
open scoped Classical

def rawSyndrome {k : ℕ} (hk : k ≤ 512) (A : Sample) (z : Candidate k) : Column :=
  fun i ↦ (z.1 i : ZMod 3329) - ∑ t, (z.2 t : ZMod 3329) * A i (t.castLE hk)

theorem raw_equation_iff_syndrome {k : ℕ} (hk : k ≤ 512)
    (A : Sample) (z : Candidate k) (c : Column) :
    (∀ i, (z.1 i : ZMod 3329) = c i +
      ∑ t, (z.2 t : ZMod 3329) * A i (t.castLE hk)) ↔ rawSyndrome hk A z = c := by
  constructor
  · intro h
    funext i
    exact sub_eq_iff_eq_add.mpr (h i)
  · intro h i
    exact sub_eq_iff_eq_add.mp (congrFun h i)

theorem rawCount_eq_fiber {k : ℕ} (hk : k ≤ 512) (T : Finset (Candidate k))
    (A : Sample) (c : Column) :
    rawCount hk T A c = (T.filter fun z ↦ rawSyndrome hk A z = c).card := by
  unfold rawCount
  exact congrArg Finset.card (filter_congr fun z _ ↦ raw_equation_iff_syndrome hk A z c)

/-- The total number of hits over all raw labels is exactly the number of candidates. -/
theorem rawCount_sum {k : ℕ} (hk : k ≤ 512) (T : Finset (Candidate k)) (A : Sample) :
    ∑ c, rawCount hk T A c = T.card := by
  simp_rw [rawCount_eq_fiber]
  have h := sum_card_fiberwise_eq_card_filter T univ (rawSyndrome hk A)
  simpa only [mem_univ, filter_true] using h

/-- Exact normalized first factorial moment under the original matrix-and-label law. -/
theorem raw_first_factorial_average {k : ℕ} (hk : k ≤ 512) (T : Finset (Candidate k)) :
    factorialAverage (rawCount hk T) 1 = (T.card : ℝ) / Fintype.card Column := by
  have hsum (A : Sample) : (∑ c, (rawCount hk T A c : ℝ)) = (T.card : ℝ) := by
    exact_mod_cast rawCount_sum hk T A
  unfold factorialAverage
  simp only [Nat.descFactorial_one, hsum, sum_const, card_univ, nsmul_eq_mul]
  have hcard : (Fintype.card Sample : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  field_simp

open CenteredPrefixOccupancy

/-- The deterministic true mean of the fixed integer slack-ball count. -/
def slackMean : ℝ := (centeredBall 119 slackRadius).card / (3329 : ℝ)^400

theorem slackMean_nonneg : 0 ≤ slackMean := by
  unfold slackMean
  positivity

theorem slack_first_factorial_average :
    factorialAverage
      (rawCount (by decide : 119 ≤ 512) (centeredBall 119 slackRadius)) 1 = slackMean := by
  rw [raw_first_factorial_average]
  have hc : Fintype.card Column = 3329^400 := by simp [Column]
  simp only [hc, Nat.cast_pow, Nat.cast_ofNat, slackMean]

/-- The concrete degree12 certificate is normalized at the actual raw mean. -/
theorem slack_mean_kernel_zero : CharlierVoidKernel.normalizedKernel 12 slackMean 0 = 1 :=
  CharlierVoidKernel.normalizedKernel_zero 12 slackMean_nonneg

/-- A rational squared radius retaining the same integer candidates but a sharper
continuous volume lower bound than evaluation at the integer cutoff itself. -/
def slackCountingRadius : ℝ := Real.sqrt (841582991 / 100)

theorem slack_counting_ball_eq :
    centeredBall 119 slackCountingRadius = centeredBall 119 slackRadius := by
  apply slackBall_eq
  · rw [slackCountingRadius, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 841582991 / 100)]
    norm_num
  · rw [slackCountingRadius, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 841582991 / 100)]
    norm_num

end SigabaNeo.Wall1.RawPrefixOccupancy

#print axioms SigabaNeo.Wall1.RawPrefixOccupancy.rawCount_sum
#print axioms SigabaNeo.Wall1.RawPrefixOccupancy.raw_first_factorial_average
#print axioms SigabaNeo.Wall1.RawPrefixOccupancy.slack_first_factorial_average
#print axioms SigabaNeo.Wall1.RawPrefixOccupancy.slack_mean_kernel_zero
#print axioms SigabaNeo.Wall1.RawPrefixOccupancy.slack_counting_ball_eq
