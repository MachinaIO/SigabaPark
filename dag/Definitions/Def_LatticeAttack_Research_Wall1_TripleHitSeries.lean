import Definitions.Def_LatticeAttack_Research_Wall1_BernoulliLogSeries
import Definitions.Def_LatticeAttack_Research_Wall1_CubicLogDefect

set_option autoImplicit true

/-! Exact cubic generating series for three events under their joint finite law. -/
noncomputable section
namespace SigabaNeo.Wall1.TripleHitSeries
open PowerSeries AffineGraphMoments RankAdditiveSeries BernoulliLogSeries CubicLogDefect
open scoped Classical
variable {Ω : Type*} [Fintype Ω] [Nonempty Ω]

def eventProbability (P : Ω → Prop) : ℝ := average (fun x ↦ if P x then 1 else 0)

def tripleSeries (P Q R : Ω → Prop) : PowerSeries ℝ :=
  seriesAverage (fun x ↦
    (if P x then (1+X : PowerSeries ℝ) else 1) *
    (if Q x then (1+X : PowerSeries ℝ) else 1) *
    (if R x then (1+X : PowerSeries ℝ) else 1))

theorem tripleSeries_eq_cubic (P Q R : Ω → Prop) :
    tripleSeries P Q R = baseline
      (eventProbability P + eventProbability Q + eventProbability R)
      (eventProbability (fun x ↦ P x ∧ Q x) + eventProbability (fun x ↦ P x ∧ R x) +
        eventProbability (fun x ↦ Q x ∧ R x))
      (eventProbability (fun x ↦ P x ∧ Q x ∧ R x)) := by
  have he : (fun x ↦
      (if P x then (1+X : PowerSeries ℝ) else 1) *
      (if Q x then (1+X : PowerSeries ℝ) else 1) *
      (if R x then (1+X : PowerSeries ℝ) else 1)) = fun x ↦
      1 + (if P x then (1 : ℝ) else 0) • X +
      (if Q x then (1 : ℝ) else 0) • X +
      (if R x then (1 : ℝ) else 0) • X +
      (if P x ∧ Q x then (1 : ℝ) else 0) • X^2 +
      (if P x ∧ R x then (1 : ℝ) else 0) • X^2 +
      (if Q x ∧ R x then (1 : ℝ) else 0) • X^2 +
      (if P x ∧ Q x ∧ R x then (1 : ℝ) else 0) • X^3 := by
    funext x
    by_cases hp : P x <;> by_cases hq : Q x <;> by_cases hr : R x <;>
      simp [hp,hq,hr] <;> ring
  unfold tripleSeries
  rw [he]
  simp only [seriesAverage_add, seriesAverage_const, seriesAverage_smul]
  simp only [smul_eq_C_mul, baseline, eventProbability, map_add]
  ring

/-- Pair factorization is explicit here; no joint independence of all three is used. -/
theorem tripleSeries_eq_perturbed (P Q R : Ω → Prop)
    (hPQ : eventProbability (fun x ↦ P x ∧ Q x) = eventProbability P * eventProbability Q)
    (hPR : eventProbability (fun x ↦ P x ∧ R x) = eventProbability P * eventProbability R)
    (hQR : eventProbability (fun x ↦ Q x ∧ R x) = eventProbability Q * eventProbability R) :
    tripleSeries P Q R = perturbed
      (eventProbability P + eventProbability Q + eventProbability R)
      (eventProbability P * eventProbability Q + eventProbability P * eventProbability R +
        eventProbability Q * eventProbability R)
      (eventProbability P * eventProbability Q * eventProbability R)
      (eventProbability (fun x ↦ P x ∧ Q x ∧ R x) -
        eventProbability P * eventProbability Q * eventProbability R) := by
  rw [tripleSeries_eq_cubic, hPQ, hPR, hQR]
  simp only [baseline, perturbed, map_sub]
  ring

end SigabaNeo.Wall1.TripleHitSeries
#print axioms SigabaNeo.Wall1.TripleHitSeries.tripleSeries_eq_cubic
#print axioms SigabaNeo.Wall1.TripleHitSeries.tripleSeries_eq_perturbed
