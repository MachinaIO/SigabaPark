import Definitions.Def_LatticeAttack_Research_Wall1_RawInputObservation
import Definitions.Def_LatticeAttack_Research_Wall1_RankAdditiveLogSupport

set_option autoImplicit true

/-! Exact support cancellation for the actual raw input-hit law under an observation rank test. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace SigabaNeo.Wall1.RawPrefixOccupancy
open Finset PowerSeries ControlledPlane TerminalProjection RankAdditiveSeries
open scoped Classical
local instance : Fact (Nat.Prime 3329) := ⟨by norm_num⟩

def inputFamilyObservation {k : ℕ} (hk : k ≤ 512) (S : Finset (Fin k → ℤ)) :
    (Sample × Column) →ₗ[ZMod 3329] (S → Column) :=
  LinearMap.pi (fun s ↦ inputObservation hk s.val)

def restrictedHitSeries {k : ℕ} (T : Finset (Candidate k))
    (S A : Finset (Fin k → ℤ)) (y : S → Column) : PowerSeries ℝ :=
  ∏ s : S, if s.val ∈ A ∧ observedInputHit T s.val (y s) then 1 + X else 1

lemma restrictedHitSeries_normalized {k : ℕ} (T : Finset (Candidate k))
    (S A : Finset (Fin k → ℤ)) (y : S → Column) :
    constantCoeff (restrictedHitSeries T S A y) = 1 := by
  unfold restrictedHitSeries
  rw [map_prod]
  apply prod_eq_one
  intro s _
  split_ifs <;> simp

lemma restrictedHitSeries_observation {k : ℕ} (hk : k ≤ 512)
    (T : Finset (Candidate k)) (S A : Finset (Fin k → ℤ)) (p : Sample × Column) :
    restrictedHitSeries T S A (inputFamilyObservation hk S p) =
      ∏ s : S, if s.val ∈ A ∧ inputHit hk T p.1 p.2 s.val then
        (1 + X : PowerSeries ℝ) else 1 := by
  unfold restrictedHitSeries
  apply prod_congr rfl
  intro s _
  simp only [inputFamilyObservation, LinearMap.pi_apply, inputHit_iff_observed]

/-- The averages are over the actual matrix and target column. The remaining
condition is an explicit rank test on their linear input observations. -/
theorem raw_mixed_log_support_zero {k : ℕ} (hk : k ≤ 512)
    (T : Finset (Candidate k)) (S R : Finset (Fin k → ℤ))
    (hS : S.Nonempty) (hR : R.Nonempty)
    (hr : Module.finrank (ZMod 3329)
        ((inputFamilyObservation hk S).prod (inputFamilyObservation hk R)).range =
      Module.finrank (ZMod 3329) (inputFamilyObservation hk S).range +
        Module.finrank (ZMod 3329) (inputFamilyObservation hk R).range) (n : ℕ) :
    (∑ A ∈ S.powerset, ∑ B ∈ R.powerset,
      (-1 : ℝ)^((S.card-A.card)+(R.card-B.card)) * coeff n (logOf
        (seriesAverage (fun p : Sample × Column ↦
          (∏ s : S, if s.val ∈ A ∧ inputHit hk T p.1 p.2 s.val then
            (1 + X : PowerSeries ℝ) else 1) *
          (∏ r : R, if r.val ∈ B ∧ inputHit hk T p.1 p.2 r.val then
            (1 + X : PowerSeries ℝ) else 1))))) = 0 := by
  have h := RankAdditiveLogSupport.mixed_log_support_zero_of_rank_additive
    (inputFamilyObservation hk S) (inputFamilyObservation hk R) hr S R hS hR
    (restrictedHitSeries T S) (restrictedHitSeries T R)
    (fun A _ y ↦ restrictedHitSeries_normalized T S A y)
    (fun B _ y ↦ restrictedHitSeries_normalized T R B y) n
  simpa only [restrictedHitSeries_observation] using h

end SigabaNeo.Wall1.RawPrefixOccupancy
#print axioms SigabaNeo.Wall1.RawPrefixOccupancy.raw_mixed_log_support_zero
