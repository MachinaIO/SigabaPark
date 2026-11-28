import Definitions.Def_LatticeAttack_Research_Wall1_RawPairObservation
import Definitions.Def_LatticeAttack_Research_Wall1_RawInputProbability
import Definitions.Def_LatticeAttack_Research_Wall1_TripleHitSeries

set_option autoImplicit true

/-! Actual pair-hit probabilities factor for distinct centered inputs. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SigabaNeo.Wall1.RawPrefixOccupancy
open Finset ControlledPlane TerminalProjection AffineGraphMoments TripleHitSeries
open scoped Classical
local instance : Fact (Nat.Prime 3329) := ⟨by norm_num⟩

theorem inputHit_pair_probability {k : ℕ} (hk : k ≤ 512)
    (T : Finset (Candidate k)) (s t : Fin k → ℤ)
    (hs : ∀ i, -1664 ≤ s i ∧ s i ≤ 1664)
    (ht : ∀ i, -1664 ≤ t i ∧ t i ≤ 1664) (hne : s ≠ t) :
    eventProbability (fun p : Sample × Column ↦
      inputHit hk T p.1 p.2 s ∧ inputHit hk T p.1 p.2 t) =
      inputHitProbability hk T s * inputHitProbability hk T t := by
  have hj := centered_inputObservation_pair_surjective hk s t hs ht hne
  have hf : Function.Surjective (inputObservation hk s) := by
    intro y
    obtain ⟨p,hp⟩ := hj (y,0)
    exact ⟨p,congrArg Prod.fst hp⟩
  have hg : Function.Surjective (inputObservation hk t) := by
    intro y
    obtain ⟨p,hp⟩ := hj (0,y)
    exact ⟨p,congrArg Prod.snd hp⟩
  have hr : Module.finrank (ZMod 3329)
      ((inputObservation hk s).prod (inputObservation hk t)).range =
      Module.finrank (ZMod 3329) (inputObservation hk s).range +
        Module.finrank (ZMod 3329) (inputObservation hk t).range := by
    rw [LinearMap.range_eq_top.mpr hj, LinearMap.range_eq_top.mpr hf,
      LinearMap.range_eq_top.mpr hg]
    simp only [finrank_top, Module.finrank_prod]
  unfold eventProbability inputHitProbability
  simp_rw [inputHit_iff_observed]
  have he (p : Sample × Column) :
      (if observedInputHit T s (inputObservation hk s p) ∧
          observedInputHit T t (inputObservation hk t p) then (1 : ℝ) else 0) =
      (if observedInputHit T s (inputObservation hk s p) then (1 : ℝ) else 0) *
        (if observedInputHit T t (inputObservation hk t p) then (1 : ℝ) else 0) := by
    split_ifs <;> simp_all
  simp_rw [he]
  exact RankAdditiveAverage.average_mul_of_rank_additive
    (inputObservation hk s) (inputObservation hk t) hr
    (fun y ↦ if observedInputHit T s y then 1 else 0)
    (fun y ↦ if observedInputHit T t y then 1 else 0)

theorem raw_tripleSeries_eq_perturbed {k : ℕ} (hk : k ≤ 512)
    (T : Finset (Candidate k)) (s t u : Fin k → ℤ)
    (hs : ∀ i, -1664 ≤ s i ∧ s i ≤ 1664)
    (ht : ∀ i, -1664 ≤ t i ∧ t i ≤ 1664)
    (hu : ∀ i, -1664 ≤ u i ∧ u i ≤ 1664)
    (hst : s ≠ t) (hsu : s ≠ u) (htu : t ≠ u) :
    tripleSeries (fun p : Sample × Column ↦ inputHit hk T p.1 p.2 s)
      (fun p ↦ inputHit hk T p.1 p.2 t) (fun p ↦ inputHit hk T p.1 p.2 u) =
      CubicLogDefect.perturbed
        (inputHitProbability hk T s + inputHitProbability hk T t + inputHitProbability hk T u)
        (inputHitProbability hk T s * inputHitProbability hk T t +
          inputHitProbability hk T s * inputHitProbability hk T u +
          inputHitProbability hk T t * inputHitProbability hk T u)
        (inputHitProbability hk T s * inputHitProbability hk T t * inputHitProbability hk T u)
        (eventProbability (fun p : Sample × Column ↦
          inputHit hk T p.1 p.2 s ∧ inputHit hk T p.1 p.2 t ∧ inputHit hk T p.1 p.2 u) -
          inputHitProbability hk T s * inputHitProbability hk T t * inputHitProbability hk T u) := by
  exact tripleSeries_eq_perturbed _ _ _
    (inputHit_pair_probability hk T s t hs ht hst)
    (inputHit_pair_probability hk T s u hs hu hsu)
    (inputHit_pair_probability hk T t u ht hu htu)

end SigabaNeo.Wall1.RawPrefixOccupancy
#print axioms SigabaNeo.Wall1.RawPrefixOccupancy.inputHit_pair_probability
#print axioms SigabaNeo.Wall1.RawPrefixOccupancy.raw_tripleSeries_eq_perturbed
