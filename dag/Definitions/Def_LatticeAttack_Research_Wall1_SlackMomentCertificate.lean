import Definitions.Def_LatticeAttack_Research_Wall1_RawPrefixMean
import Definitions.Def_LatticeAttack_Research_Wall1_CharlierReference
import Definitions.Def_LatticeAttack_Research_Wall1_CanonicalFactorialCorrection

set_option autoImplicit true

/-! # Concrete conditional moment certificate for high-radius exits

All geometry, candidate sets, polynomial coefficients and means are fixed to
the actual restart. The final theorem constructs the factorial corrections
canonically, leaving only their quantitative bounds as explicit hypotheses.
-/

noncomputable section
namespace SigabaNeo.Wall1.SlackMomentCertificate
open Finset ControlledPlane TerminalProjection RawPrefixOccupancy
open CenteredPrefixOccupancy CharlierVoidKernel FactorialMomentTransfer

abbrev slackCount := rawCount (by decide : 119 ≤ 512) (centeredBall 119 slackRadius)

def exitSet : Finset Sample := gatedExitSet
  (fun i A ↦ 12 * (3329 : ℝ)^386 ≤ retainedDeterminant A (entry i))
  (fun i A ↦ actualSlackRadius A (entry i))

def exitProbability : ℝ := (exitSet.card : ℝ) / Fintype.card Sample

def normalizedSquareCoefficient (h : ℕ) : ℝ :=
  squareCoefficient slackMean h / partialExp 12 slackMean ^ 2

def correctionBound (E : ℕ → ℝ) : ℝ :=
  differenceWeight (range 25) normalizedSquareCoefficient slackMean 0 +
    ∑ k ∈ range 25, |differenceWeight (range 25) normalizedSquareCoefficient slackMean k| * E k

/-- Conditional high-radius probability bound; the two moment hypotheses are still
substantive production obligations. No low-radius history is covered. -/
theorem exit_probability_le_of_corrections (d E : ℕ → ℝ)
    (hF : ∀ h ∈ range 25, factorialAverage slackCount h =
      ∑ k ∈ range 25, d k * transferCoefficient slackMean h k)
    (herr : ∀ k ∈ range 25, |d k - (if k = 0 then 1 else 0)| ≤ E k) :
    exitProbability ≤ (25 / 7) * correctionBound E := by
  have havg := square_average_le_transfer slackCount (normalizedKernel 12 slackMean)
    (range 25) (by simp) normalizedSquareCoefficient d E slackMean
    (normalizedKernel12_square_collected slackMean) hF herr
  change _ ≤ correctionBound E at havg
  have hcount := actual_slack_exit_le_degree12 slackMean_nonneg
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hcount
  have hΩ : 0 < (Fintype.card Sample : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hC : 0 < (Fintype.card Column : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hsum := (div_le_iff₀ (mul_pos hΩ hC)).mp havg
  unfold exitProbability exitSet
  apply (div_le_iff₀ hΩ).2
  apply (mul_le_mul_iff_right₀ hC).mp
  nlinarith

/-- Corrections determined by the actual moments, rather than supplied by a caller. -/
def actualCorrection : ℕ → ℝ := canonicalCorrection (factorialAverage slackCount) slackMean

theorem actualCorrection_zero : actualCorrection 0 = 1 := by
  rw [actualCorrection, canonicalCorrection_zero, factorialAverage_zero]

theorem actualCorrection_one : actualCorrection 1 = 0 := by
  rw [actualCorrection, canonicalCorrection_one, factorialAverage_zero]
  have h := slack_first_factorial_average
  change factorialAverage slackCount 1 = slackMean at h
  rw [h]
  ring

/-- The actual convolution is discharged by construction. Only quantitative bounds
on the corrections of orders2 through24 remain as hypotheses. -/
theorem exit_probability_le_higher_corrections (E : ℕ → ℝ)
    (herr : ∀ k, 2 ≤ k → k ≤ 24 → |actualCorrection k| ≤ E k) :
    exitProbability ≤ (25 / 7) * correctionBound (fun k ↦ if 2 ≤ k then E k else 0) := by
  apply exit_probability_le_of_corrections actualCorrection
  · intro h hh
    exact canonical_convolution_range (factorialAverage slackCount) slackMean
      (show h ≤ 24 by have := mem_range.mp hh; omega)
  · intro k hk
    by_cases h : 2 ≤ k
    · have hk0 : k ≠ 0 := by omega
      simpa only [h, ite_true, hk0, ite_false, sub_zero] using
        herr k h (by have := mem_range.mp hk; omega)
    · have hk01 : k = 0 ∨ k = 1 := by omega
      rcases hk01 with rfl | rfl <;> simp [actualCorrection_zero, actualCorrection_one]

/-- The weighted higher-order correction in exit-probability units. -/
def correctionCharge (E : ℕ → ℝ) : ℝ := (25 / 7) *
  ∑ k ∈ range 25, |differenceWeight (range 25) normalizedSquareCoefficient slackMean k| *
    (if 2 ≤ k then E k else 0)

theorem exit_probability_lt_reference_add
    (hmean : 58.5115 ≤ slackMean) (E : ℕ → ℝ)
    (herr : ∀ k, 2 ≤ k → k ≤ 24 → |actualCorrection k| ≤ E k) :
    exitProbability < (84896 / 100000000000000000 : ℝ) + correctionCharge E := by
  have h := exit_probability_le_higher_corrections E herr
  have hw : differenceWeight (range 25) normalizedSquareCoefficient slackMean 0 =
      1 / partialExp 12 slackMean := normalized_reference_weight12 slackMean_nonneg
  rw [correctionBound, hw, mul_add] at h
  have he : (25 / 7 : ℝ) * (1 / partialExp 12 slackMean) =
      1 / ((7 / 25) * partialExp 12 slackMean) := by ring
  rw [he] at h
  unfold correctionCharge
  linarith [degree12_reference_bound_sharp hmean]

/-- Conditional numerical target. The mean lower bound, correction bounds, and
their weighted numerical charge are not proved by this theorem. -/
theorem exit_probability_lt_target
    (hmean : 58.5115 ≤ slackMean) (E : ℕ → ℝ)
    (herr : ∀ k, 2 ≤ k → k ≤ 24 → |actualCorrection k| ≤ E k)
    (hcharge : correctionCharge E ≤ (225039 / 1000000000000000000 : ℝ)) :
    exitProbability < (1074 / 1000000000000000 : ℝ) := by
  have h := exit_probability_lt_reference_add hmean E herr
  linarith

end SigabaNeo.Wall1.SlackMomentCertificate

#print axioms SigabaNeo.Wall1.SlackMomentCertificate.exit_probability_le_of_corrections
#print axioms SigabaNeo.Wall1.SlackMomentCertificate.actualCorrection_zero
#print axioms SigabaNeo.Wall1.SlackMomentCertificate.actualCorrection_one
#print axioms SigabaNeo.Wall1.SlackMomentCertificate.exit_probability_le_higher_corrections
#print axioms SigabaNeo.Wall1.SlackMomentCertificate.exit_probability_lt_target
