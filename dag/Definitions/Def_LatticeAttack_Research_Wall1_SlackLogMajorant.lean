import Definitions.Def_LatticeAttack_Research_Wall1_FiniteExponentialReconstruction
import Definitions.Def_LatticeAttack_Research_Wall1_SlackThirdOrderTarget

set_option autoImplicit true

/-! Logarithmic coordinates of the actual canonical correction sequence.
These coordinates are defined by finite triangular inversion. Identifying their
higher-order bounds with geometric incidence estimates remains a separate task. -/
noncomputable section
namespace SigabaNeo.Wall1.SlackMomentCertificate
open ExponentialCoefficientRecurrence

def actualLogCoefficient : ℕ → ℝ := logarithmicCoefficient actualCorrection

theorem actualLogCoefficient_zero : actualLogCoefficient 0 = 0 :=
  logarithmicCoefficient_zero _

theorem actualLogCoefficient_one : actualLogCoefficient 1 = 0 := by
  rw [actualLogCoefficient, logarithmicCoefficient_one, actualCorrection_one]

theorem actualLogCoefficient_two : actualLogCoefficient 2 = actualCorrection 2 := by
  rw [actualLogCoefficient, logarithmicCoefficient_two, actualCorrection_one]
  ring

theorem actualLogCoefficient_two_bound : |actualLogCoefficient 2| ≤ (1:ℝ)/10^297 := by
  rw [actualLogCoefficient_two]
  exact actualCorrection_two_le_numeric

/-- The actual corrections are reconstructed by the exponential coefficient recurrence. -/
theorem actualCorrection_eq_exponential (n : ℕ) :
    actualCorrection n = exponentialCoefficient actualLogCoefficient n :=
  (exponential_logarithmicCoefficient _ actualCorrection_zero n).symm

/-- Quantitative logarithmic bounds suffice for the actual higher corrections. -/
theorem actualCorrection_le_log_majorant (A : ℕ → ℝ)
    (hA : ∀ j, 1 ≤ j → j ≤ 24 → |actualLogCoefficient j| ≤ A j)
    {n : ℕ} (hn : n ≤ 24) :
    |actualCorrection n| ≤ exponentialCoefficient A n := by
  rw [actualCorrection_eq_exponential]
  exact exponentialCoefficient_abs_le _ A hA n hn

/-- High-radius target expressed in logarithmic bounds, with proved mean and second order. -/
theorem exit_probability_lt_target_from_log_majorant (A : ℕ → ℝ)
    (hA : ∀ j, 1 ≤ j → j ≤ 24 → |actualLogCoefficient j| ≤ A j)
    (hcharge : correctionCharge (withCertifiedSecond (exponentialCoefficient A)) ≤
      (225039 / 1000000000000000000 : ℝ)) :
    exitProbability < (1074 / 1000000000000000 : ℝ) := by
  apply exit_probability_lt_target_from_third_order (exponentialCoefficient A) ?_ hcharge
  intro k hk hmax
  exact actualCorrection_le_log_majorant A hA hmax

/-- Exact finite polynomial reconstruction through degree24. -/
theorem actualCorrection_eq_finiteExp {n : ℕ} (hn : n ≤ 24) :
    actualCorrection n = FiniteConvolutionMajorant.finiteExp actualLogCoefficient 24 n :=
  (finiteExp_logarithmicCoefficient _ actualCorrection_zero 24 n hn).symm

/-- The finite exponential used for coefficient envelopes bounds the actual correction. -/
theorem actualCorrection_le_finiteExp (A : ℕ → ℝ) (hzero : A 0 = 0)
    (hA : ∀ j, 1 ≤ j → j ≤ 24 → |actualLogCoefficient j| ≤ A j)
    {n : ℕ} (hn : n ≤ 24) :
    |actualCorrection n| ≤ FiniteConvolutionMajorant.finiteExp A 24 n := by
  rw [actualCorrection_eq_finiteExp hn]
  apply FiniteConvolutionMajorant.finiteExp_abs_le _ A hn
  intro i hi
  by_cases hz : i = 0
  · subst i
    simp only [actualLogCoefficient_zero, abs_zero, hzero, le_refl]
  · exact hA i (by omega) hi

/-- Finite-exponential envelope version of the gated high-radius target. -/
theorem exit_probability_lt_target_from_finiteExp (A : ℕ → ℝ) (hzero : A 0 = 0)
    (hA : ∀ j, 1 ≤ j → j ≤ 24 → |actualLogCoefficient j| ≤ A j)
    (hcharge : correctionCharge
      (withCertifiedSecond (FiniteConvolutionMajorant.finiteExp A 24)) ≤
      (225039 / 1000000000000000000 : ℝ)) :
    exitProbability < (1074 / 1000000000000000 : ℝ) := by
  apply exit_probability_lt_target_from_third_order
    (FiniteConvolutionMajorant.finiteExp A 24) ?_ hcharge
  intro k hk hmax
  exact actualCorrection_le_finiteExp A hzero hA hmax

end SigabaNeo.Wall1.SlackMomentCertificate
#print axioms SigabaNeo.Wall1.SlackMomentCertificate.actualCorrection_eq_exponential
#print axioms SigabaNeo.Wall1.SlackMomentCertificate.actualCorrection_le_log_majorant
#print axioms SigabaNeo.Wall1.SlackMomentCertificate.exit_probability_lt_target_from_log_majorant

#print axioms SigabaNeo.Wall1.SlackMomentCertificate.exit_probability_lt_target_from_finiteExp
