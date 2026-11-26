import Definitions.Def_LatticeAttack_Research_Wall1_RawExactSupport

set_option autoImplicit true

/-! All-order log coefficients of a single finite-law indicator. -/
noncomputable section
namespace SigabaNeo.Wall1.BernoulliLogSeries
open Finset PowerSeries RankAdditiveSeries AffineGraphMoments
open scoped Classical

lemma seriesAverage_const {Ω : Type*} [Fintype Ω] [Nonempty Ω] (F : PowerSeries ℝ) :
    seriesAverage (fun _ : Ω ↦ F) = F := by
  ext n
  have hc : (Fintype.card Ω : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp [coeff_seriesAverage, average, hc]

lemma seriesAverage_add {Ω : Type*} [Fintype Ω] (F G : Ω → PowerSeries ℝ) :
    seriesAverage (fun x ↦ F x + G x) = seriesAverage F + seriesAverage G := by
  ext n
  simp [coeff_seriesAverage, average, sum_add_distrib, add_div]

lemma seriesAverage_smul {Ω : Type*} [Fintype Ω] (a : Ω → ℝ) (F : PowerSeries ℝ) :
    seriesAverage (fun x ↦ a x • F) = average a • F := by
  ext n
  simp only [coeff_seriesAverage, map_smul, smul_eq_mul, average, ← sum_mul]
  ring

theorem seriesAverage_indicator {Ω : Type*} [Fintype Ω] [Nonempty Ω] (P : Ω → Prop) :
    seriesAverage (fun x ↦ if P x then (1 + X : PowerSeries ℝ) else 1) =
      1 + average (fun x ↦ if P x then (1 : ℝ) else 0) • X := by
  have he : (fun x ↦ if P x then (1 + X : PowerSeries ℝ) else 1) =
      fun x ↦ 1 + (if P x then (1 : ℝ) else 0) • (X : PowerSeries ℝ) := by
    funext x
    by_cases h : P x <;> simp [h]
  rw [he, seriesAverage_add, seriesAverage_const, seriesAverage_smul]

theorem coeff_logOf_one_add_smul_X (p : ℝ) (n : ℕ) :
    coeff (n+1) (logOf (1 + p • (X : PowerSeries ℝ))) =
      p^(n+1) * ((-1 : ℝ)^(n+2) / (n+1)) := by
  rw [logOf_eq, add_sub_cancel_left, ← rescale_eq_subst, coeff_rescale]
  simp [coeff_log]

theorem indicator_log_coeff {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (P : Ω → Prop) (n : ℕ) :
    coeff (n+1) (logOf (seriesAverage
      (fun x ↦ if P x then (1 + X : PowerSeries ℝ) else 1))) =
      (average (fun x ↦ if P x then (1 : ℝ) else 0))^(n+1) *
        ((-1 : ℝ)^(n+2) / (n+1)) := by
  rw [seriesAverage_indicator, coeff_logOf_one_add_smul_X]

end SigabaNeo.Wall1.BernoulliLogSeries
#print axioms SigabaNeo.Wall1.BernoulliLogSeries.indicator_log_coeff
