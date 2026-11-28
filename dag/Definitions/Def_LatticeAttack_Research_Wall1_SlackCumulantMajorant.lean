import Definitions.Def_LatticeAttack_Research_Wall1_FormalCumulantBridge
import Definitions.Def_LatticeAttack_Research_Wall1_SlackLogMajorant

set_option autoImplicit true

/-! Actual factorial cumulant bounds feed the verified finite correction envelope. -/
noncomputable section
namespace SigabaNeo.Wall1.SlackMomentCertificate
open FactorialMomentTransfer RawPrefixOccupancy

def actualFactorialCumulant : ℕ → ℝ := factorialCumulant (factorialAverage slackCount)

/-- Above degree one, the logarithmic corrections are factorial cumulants divided by n!. -/
theorem actualLogCoefficient_eq_cumulant {n : ℕ} (hn : 2 ≤ n) :
    actualLogCoefficient n = actualFactorialCumulant n / (n.factorial : ℝ) :=
  logarithmicCorrection_eq_cumulant _ _ (factorialAverage_zero _) hn

/-- Insert the proved zero/first/second coefficients, and normalize higher cumulant bounds. -/
def cumulantLogEnvelope (B : ℕ → ℝ) (j : ℕ) : ℝ :=
  if j < 2 then 0 else if j = 2 then 1/10^297 else B j / (j.factorial : ℝ)

theorem actualLogCoefficient_le_cumulant_envelope (B : ℕ → ℝ)
    (hB : ∀ j, 3 ≤ j → j ≤ 24 → |actualFactorialCumulant j| ≤ B j)
    {j : ℕ} (hj : 1 ≤ j) (hmax : j ≤ 24) :
    |actualLogCoefficient j| ≤ cumulantLogEnvelope B j := by
  by_cases hsmall : j < 2
  · have he : j = 1 := by omega
    subst j
    simp [cumulantLogEnvelope, actualLogCoefficient_one]
  · by_cases he : j = 2
    · subst j
      simpa only [cumulantLogEnvelope, show ¬ (2 < 2) from by omega,
        ite_false, ite_true] using actualLogCoefficient_two_bound
    · rw [cumulantLogEnvelope, if_neg hsmall, if_neg he,
        actualLogCoefficient_eq_cumulant (by omega), abs_div,
        abs_of_nonneg (show (0:ℝ) ≤ (j.factorial : ℝ) from Nat.cast_nonneg _)]
      exact div_le_div_of_nonneg_right (hB j (by omega) hmax) (Nat.cast_nonneg _)

/-- Exact cumulant normalization supplies the finite exponential correction envelope. -/
theorem actualCorrection_le_cumulant_envelope (B : ℕ → ℝ)
    (hB : ∀ j, 3 ≤ j → j ≤ 24 → |actualFactorialCumulant j| ≤ B j)
    {n : ℕ} (hn : n ≤ 24) :
    |actualCorrection n| ≤ FiniteConvolutionMajorant.finiteExp (cumulantLogEnvelope B) 24 n := by
  apply actualCorrection_le_finiteExp _ (by simp [cumulantLogEnvelope]) ?_ hn
  intro j hj hmax
  exact actualLogCoefficient_le_cumulant_envelope B hB hj hmax

/-- High-radius target conditional only on higher cumulant bounds and the completed charge. -/
theorem exit_probability_lt_target_from_cumulants (B : ℕ → ℝ)
    (hB : ∀ j, 3 ≤ j → j ≤ 24 → |actualFactorialCumulant j| ≤ B j)
    (hcharge : correctionCharge (withCertifiedSecond
      (FiniteConvolutionMajorant.finiteExp (cumulantLogEnvelope B) 24)) ≤
      (225039 / 1000000000000000000 : ℝ)) :
    exitProbability < (1074 / 1000000000000000 : ℝ) := by
  apply exit_probability_lt_target_from_finiteExp _ (by simp [cumulantLogEnvelope]) ?_ hcharge
  intro j hj hmax
  exact actualLogCoefficient_le_cumulant_envelope B hB hj hmax

end SigabaNeo.Wall1.SlackMomentCertificate
#print axioms SigabaNeo.Wall1.SlackMomentCertificate.actualLogCoefficient_eq_cumulant
#print axioms SigabaNeo.Wall1.SlackMomentCertificate.exit_probability_lt_target_from_cumulants
