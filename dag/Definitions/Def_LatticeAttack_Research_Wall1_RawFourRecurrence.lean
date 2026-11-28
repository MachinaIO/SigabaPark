import Definitions.Def_LatticeAttack_Research_Wall1_RawFourLogDefect
import Definitions.Def_LatticeAttack_Research_Wall1_FourLogRecurrence

set_option autoImplicit true

/-! The four-input recurrence under the actual fixed-family input-hit law. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SigabaNeo.Wall1.RawPrefixOccupancy
open Finset PowerSeries ControlledPlane TerminalProjection RankAdditiveSeries
open ExactSupportReconstruction FourLogRecurrence
open scoped Classical

def inputHitSeries {k : ℕ} (hk : k ≤ 512) (T : Finset (Candidate k))
    (S : Finset (Fin k → ℤ)) : PowerSeries ℝ :=
  seriesAverage (fun p : Sample × Column ↦
    ∏ s ∈ S, if inputHit hk T p.1 p.2 s then (1+X : PowerSeries ℝ) else 1)

theorem inputHitSeries_constant {k : ℕ} (hk : k ≤ 512) (T : Finset (Candidate k))
    (S : Finset (Fin k → ℤ)) : constantCoeff (inputHitSeries hk T S) = 1 := by
  apply RankAdditiveLogSupport.constantCoeff_seriesAverage_one
  intro p
  simp only [map_prod]
  apply prod_eq_one
  intro s _
  split_ifs <;> simp

theorem rawTripleLogDefect_eq_inputSeries {k : ℕ} (hk : k ≤ 512)
    (T : Finset (Candidate k)) (a b c : Fin k → ℤ)
    (ha : ∀ i, -1664 ≤ a i ∧ a i ≤ 1664)
    (hb : ∀ i, -1664 ≤ b i ∧ b i ≤ 1664)
    (hc : ∀ i, -1664 ≤ c i ∧ c i ≤ 1664)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    rawTripleLogDefect hk T a b c = logOf (inputHitSeries hk T {a,b,c}) -
      (logOf (1+C (inputHitProbability hk T a)*X) +
       logOf (1+C (inputHitProbability hk T b)*X) +
       logOf (1+C (inputHitProbability hk T c)*X)) := by
  ext n
  rw [← rawExactSupport_triple_eq_logDefect hk T a b c ha hb hc hab hac hbc]
  have he := exactSupport_triple_of_pair_zero (rawInputLogCoeff hk T n) a b c
    hab hac hbc (rawInputLogCoeff_empty hk T n)
    (rawExactSupport_centered_pair_zero hk T a b ha hb hab n)
    (rawExactSupport_centered_pair_zero hk T a c ha hc hac n)
    (rawExactSupport_centered_pair_zero hk T b c hb hc hbc n)
  change rawExactSupport hk T n {a,b,c} = _ at he
  rw [he]
  simp only [rawInputLogCoeff_singleton_series, map_sub, map_add]
  change _ - _ - _ - _ = _ - (_ + _ + _)
  change coeff n (logOf (inputHitSeries hk T {a,b,c})) - _ - _ - _ = _
  ring

theorem rawFourLogDefect_eq_correction {k : ℕ} (hk : k ≤ 512)
    (T : Finset (Candidate k)) (s : Fin 4 → Fin k → ℤ)
    (hc : ∀ j i, -1664 ≤ s j i ∧ s j i ≤ 1664) (hi : Function.Injective s) :
    rawFourLogDefect hk T (s 0) (s 1) (s 2) (s 3) =
      correction (inputHitSeries hk T {s 0,s 1,s 2,s 3})
        ((1+C (inputHitProbability hk T (s 0))*X) *
         (1+C (inputHitProbability hk T (s 1))*X) *
         (1+C (inputHitProbability hk T (s 2))*X) *
         (1+C (inputHitProbability hk T (s 3))*X))
        (inputHitSeries hk T {s 0,s 1,s 2}) (inputHitSeries hk T {s 0,s 1,s 3})
        (inputHitSeries hk T {s 0,s 2,s 3}) (inputHitSeries hk T {s 1,s 2,s 3}) := by
  rw [correction_eq_subtract_proper _ _ _ _ _ _ _ _ _
    (by simp) (by simp) (by simp) (by simp)]
  unfold rawFourLogDefect
  rw [rawTripleLogDefect_eq_inputSeries hk T _ _ _ (hc 0) (hc 1) (hc 2)
      (hi.ne (by decide)) (hi.ne (by decide)) (hi.ne (by decide)),
    rawTripleLogDefect_eq_inputSeries hk T _ _ _ (hc 0) (hc 1) (hc 3)
      (hi.ne (by decide)) (hi.ne (by decide)) (hi.ne (by decide)),
    rawTripleLogDefect_eq_inputSeries hk T _ _ _ (hc 0) (hc 2) (hc 3)
      (hi.ne (by decide)) (hi.ne (by decide)) (hi.ne (by decide)),
    rawTripleLogDefect_eq_inputSeries hk T _ _ _ (hc 1) (hc 2) (hc 3)
      (hi.ne (by decide)) (hi.ne (by decide)) (hi.ne (by decide))]
  rfl

/-- An exact recurrence for actual four-input supports, with no independence beyond proved pairs. -/
theorem rawExactSupport_four_recurrence {k : ℕ} (hk : k ≤ 512)
    (T : Finset (Candidate k)) (s : Fin 4 → Fin k → ℤ)
    (hc : ∀ j i, -1664 ≤ s j i ∧ s j i ≤ 1664) (hi : Function.Injective s) (n : ℕ) :
    let F := inputHitSeries hk T {s 0,s 1,s 2,s 3}
    let B := (1+C (inputHitProbability hk T (s 0))*X) *
      (1+C (inputHitProbability hk T (s 1))*X) *
      (1+C (inputHitProbability hk T (s 2))*X) *
      (1+C (inputHitProbability hk T (s 3))*X)
    let G₁ := inputHitSeries hk T {s 0,s 1,s 2}
    let G₂ := inputHitSeries hk T {s 0,s 1,s 3}
    let G₃ := inputHitSeries hk T {s 0,s 2,s 3}
    let G₄ := inputHitSeries hk T {s 1,s 2,s 3}
    (n+1 : ℝ) * rawExactSupport hk T (n+1) {s 0,s 1,s 2,s 3} =
      coeff n (source F B G₁ G₂ G₃ G₄) -
        ∑ i ∈ range n, ((i+1 : ℝ) * rawExactSupport hk T (i+1) {s 0,s 1,s 2,s 3}) *
          coeff (n-i) (denominator F B G₁ G₂ G₃ G₄) := by
  dsimp only
  simp_rw [rawExactSupport_four_eq_logDefect hk T _ _ _ _ (hc 0) (hc 1) (hc 2) (hc 3)
    (hi.ne (by decide)) (hi.ne (by decide)) (hi.ne (by decide))
    (hi.ne (by decide)) (hi.ne (by decide)) (hi.ne (by decide)),
    rawFourLogDefect_eq_correction hk T s hc hi]
  apply correction_coefficient_recurrence
  · exact inputHitSeries_constant _ _ _
  · simp
  · exact inputHitSeries_constant _ _ _
  · exact inputHitSeries_constant _ _ _
  · exact inputHitSeries_constant _ _ _
  · exact inputHitSeries_constant _ _ _

end SigabaNeo.Wall1.RawPrefixOccupancy
#print axioms SigabaNeo.Wall1.RawPrefixOccupancy.rawFourLogDefect_eq_correction

#print axioms SigabaNeo.Wall1.RawPrefixOccupancy.rawExactSupport_four_recurrence
