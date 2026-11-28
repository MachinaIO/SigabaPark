import Definitions.Def_LatticeAttack_Research_Wall1_TripleHitSeries

set_option autoImplicit true

/-! Exact four-event generating series under a shared finite probability law. -/
noncomputable section
namespace SigabaNeo.Wall1.FourHitSeries
open PowerSeries RankAdditiveSeries BernoulliLogSeries TripleHitSeries
open scoped Classical
variable {Ω : Type*} [Fintype Ω] [Nonempty Ω]

def fourSeries (P Q R S : Ω → Prop) : PowerSeries ℝ :=
  seriesAverage (fun x ↦
    (if P x then (1+X : PowerSeries ℝ) else 1) *
    (if Q x then (1+X : PowerSeries ℝ) else 1) *
    (if R x then (1+X : PowerSeries ℝ) else 1) *
    (if S x then (1+X : PowerSeries ℝ) else 1))

theorem fourSeries_eq_quartic (P Q R S : Ω → Prop) :
    fourSeries P Q R S = 1 +
      C (eventProbability P + eventProbability Q + eventProbability R + eventProbability S) * X +
      C ((eventProbability (fun x ↦ P x ∧ Q x)) + (eventProbability (fun x ↦ P x ∧ R x)) + (eventProbability (fun x ↦ P x ∧ S x)) + (eventProbability (fun x ↦ Q x ∧ R x)) + (eventProbability (fun x ↦ Q x ∧ S x)) + (eventProbability (fun x ↦ R x ∧ S x))) * X^2 +
      C ((eventProbability (fun x ↦ P x ∧ Q x ∧ R x)) + (eventProbability (fun x ↦ P x ∧ Q x ∧ S x)) + (eventProbability (fun x ↦ P x ∧ R x ∧ S x)) + (eventProbability (fun x ↦ Q x ∧ R x ∧ S x))) * X^3 +
      C ((eventProbability (fun x ↦ P x ∧ Q x ∧ R x ∧ S x))) * X^4 := by
  have he : (fun x ↦
    (if P x then (1+X : PowerSeries ℝ) else 1) *
    (if Q x then (1+X : PowerSeries ℝ) else 1) *
    (if R x then (1+X : PowerSeries ℝ) else 1) *
    (if S x then (1+X : PowerSeries ℝ) else 1)) = fun x ↦
      1 + (if P x then (1 : ℝ) else 0) • X +
      (if Q x then (1 : ℝ) else 0) • X +
      (if R x then (1 : ℝ) else 0) • X +
      (if S x then (1 : ℝ) else 0) • X +
      (if P x ∧ Q x then (1 : ℝ) else 0) • X^2 +
      (if P x ∧ R x then (1 : ℝ) else 0) • X^2 +
      (if P x ∧ S x then (1 : ℝ) else 0) • X^2 +
      (if Q x ∧ R x then (1 : ℝ) else 0) • X^2 +
      (if Q x ∧ S x then (1 : ℝ) else 0) • X^2 +
      (if R x ∧ S x then (1 : ℝ) else 0) • X^2 +
      (if P x ∧ Q x ∧ R x then (1 : ℝ) else 0) • X^3 +
      (if P x ∧ Q x ∧ S x then (1 : ℝ) else 0) • X^3 +
      (if P x ∧ R x ∧ S x then (1 : ℝ) else 0) • X^3 +
      (if Q x ∧ R x ∧ S x then (1 : ℝ) else 0) • X^3 +
      (if P x ∧ Q x ∧ R x ∧ S x then (1 : ℝ) else 0) • X^4 := by
    funext x
    by_cases hp : P x <;> by_cases hq : Q x <;>
      by_cases hr : R x <;> by_cases hs : S x <;>
      simp [hp,hq,hr,hs] <;> ring
  unfold fourSeries
  rw [he]
  simp only [seriesAverage_add, seriesAverage_const, seriesAverage_smul]
  simp only [smul_eq_C_mul, eventProbability, map_add]
  ring

def tripleEventDefect (P Q R : Ω → Prop) : ℝ :=
  eventProbability (fun x ↦ P x ∧ Q x ∧ R x) -
    eventProbability P * eventProbability Q * eventProbability R

def connectedFourthDefect (P Q R S : Ω → Prop) : ℝ :=
  eventProbability (fun x ↦ P x ∧ Q x ∧ R x ∧ S x) -
    eventProbability P * eventProbability Q * eventProbability R * eventProbability S -
    (eventProbability P * tripleEventDefect Q R S +
     eventProbability Q * tripleEventDefect P R S +
     eventProbability R * tripleEventDefect P Q S +
     eventProbability S * tripleEventDefect P Q R)

/-- Only the six pair factorizations are assumed; triple and quadruple dependence is retained. -/
theorem fourSeries_eq_corrected (P Q R S : Ω → Prop)
    (hPQ : eventProbability (fun x ↦ P x ∧ Q x) =
      eventProbability P * eventProbability Q)
    (hPR : eventProbability (fun x ↦ P x ∧ R x) =
      eventProbability P * eventProbability R)
    (hPS : eventProbability (fun x ↦ P x ∧ S x) =
      eventProbability P * eventProbability S)
    (hQR : eventProbability (fun x ↦ Q x ∧ R x) =
      eventProbability Q * eventProbability R)
    (hQS : eventProbability (fun x ↦ Q x ∧ S x) =
      eventProbability Q * eventProbability S)
    (hRS : eventProbability (fun x ↦ R x ∧ S x) =
      eventProbability R * eventProbability S) :
    fourSeries P Q R S =
      (1+C (eventProbability P)*X)*(1+C (eventProbability Q)*X)*
      (1+C (eventProbability R)*X)*(1+C (eventProbability S)*X) +
      C (tripleEventDefect Q R S + tripleEventDefect P R S +
         tripleEventDefect P Q S + tripleEventDefect P Q R)*X^3 +
      C (connectedFourthDefect P Q R S +
        eventProbability P * tripleEventDefect Q R S +
        eventProbability Q * tripleEventDefect P R S +
        eventProbability R * tripleEventDefect P Q S +
        eventProbability S * tripleEventDefect P Q R)*X^4 := by
  rw [fourSeries_eq_quartic, hPQ, hPR, hPS, hQR, hQS, hRS]
  simp only [tripleEventDefect, connectedFourthDefect, map_add, map_sub, map_mul]
  ring

end SigabaNeo.Wall1.FourHitSeries
#print axioms SigabaNeo.Wall1.FourHitSeries.fourSeries_eq_quartic

#print axioms SigabaNeo.Wall1.FourHitSeries.fourSeries_eq_corrected
