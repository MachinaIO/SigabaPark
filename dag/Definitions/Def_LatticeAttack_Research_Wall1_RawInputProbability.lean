import Definitions.Def_LatticeAttack_Research_Wall1_RawSingletonSupport
import Definitions.Def_LatticeAttack_Research_Wall1_SlackInputPowerBound

set_option autoImplicit true

/-! The actual single-input hit probability is the centered fiber size divided by q^400. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SigabaNeo.Wall1.RawPrefixOccupancy
open Finset ControlledPlane TerminalProjection FactorialMomentTransfer AffineGraphMoments
open scoped Classical

theorem rawCount_inputFiber {k : ℕ} (hk : k ≤ 512) (T : Finset (Candidate k))
    (hT : ∀ z ∈ T, ∀ i, -1664 ≤ z.1 i ∧ z.1 i ≤ 1664)
    (s : Fin k → ℤ) (A : Sample) (c : Column) :
    rawCount hk (T.filter fun z ↦ z.2 = s) A c = if inputHit hk T A c s then 1 else 0 := by
  rw [rawCount_eq_inputHit_card hk _ (fun z hz ↦ hT z (mem_filter.mp hz).1)]
  have he : (((T.filter fun z ↦ z.2 = s).image Prod.snd).filter
      (inputHit hk (T.filter fun z ↦ z.2 = s) A c)) =
      if inputHit hk T A c s then {s} else ∅ := by
    ext t
    simp only [mem_filter, mem_image, inputHit]
    split_ifs with h
    · simp only [mem_singleton]
      constructor
      · rintro ⟨⟨z,⟨_,hs⟩,ht⟩,_⟩
        exact ht.symm.trans hs
      · intro ht
        subst t
        obtain ⟨z,hz,hs,hc⟩ := h
        exact ⟨⟨z,⟨hz,hs⟩,hs⟩,⟨z,⟨hz,hs⟩,hs,hc⟩⟩
    · simp only [notMem_empty, iff_false]
      rintro ⟨_,⟨z,⟨hz,hs⟩,_,hc⟩⟩
      exact h ⟨z,hz,hs,hc⟩
  rw [he]
  split_ifs <;> simp

theorem inputHitProbability_eq_fiber {k : ℕ} (hk : k ≤ 512)
    (T : Finset (Candidate k))
    (hT : ∀ z ∈ T, ∀ i, -1664 ≤ z.1 i ∧ z.1 i ≤ 1664) (s : Fin k → ℤ) :
    inputHitProbability hk T s =
      ((T.filter fun z ↦ z.2 = s).card : ℝ) / Fintype.card Column := by
  rw [← raw_first_factorial_average hk (T.filter fun z ↦ z.2 = s)]
  unfold inputHitProbability average factorialAverage
  simp only [Fintype.card_prod, Nat.cast_mul, Fintype.sum_prod_type,
    Nat.descFactorial_one, rawCount_inputFiber hk T hT s]
  simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero]

end SigabaNeo.Wall1.RawPrefixOccupancy
namespace SigabaNeo.Wall1.SlackMomentCertificate
open Finset RawPrefixOccupancy CenteredPrefixOccupancy CandidateInputPairs
open ControlledPlane TerminalProjection
open scoped Classical

theorem slack_inputHitProbability_power_sum_le (n : ℕ) :
    (∑ s ∈ (centeredBall 119 slackRadius).image Prod.snd,
      (inputHitProbability (by decide : 119 ≤ 512) (centeredBall 119 slackRadius) s)^(n+1)) ≤
        119 * ((9 : ℝ)/10^300)^n := by
  have hT := fun (z : Candidate 119) (hz : z ∈ centeredBall 119 slackRadius) ↦
    ((mem_centeredBall slackRadius z).mp hz).1
  simp_rw [inputHitProbability_eq_fiber (by decide : 119 ≤ 512)
    (centeredBall 119 slackRadius) hT, div_pow]
  rw [← sum_div]
  have hc : Fintype.card Column = 3329^400 := by simp [Column]
  rw [hc]
  convert slack_inputPowerSum_le_numeric n using 1 <;>
    simp [inputPowerSum, Nat.cast_sum, Nat.cast_pow, div_pow]

theorem slack_singleton_cumulant_sum_abs_le (n : ℕ) :
    (∑ s ∈ (centeredBall 119 slackRadius).image Prod.snd,
      |((n+1).factorial : ℝ) * rawExactSupport (by decide : 119 ≤ 512)
        (centeredBall 119 slackRadius) (n+1) {s}|) ≤
      (n.factorial : ℝ) * (119 * ((9 : ℝ)/10^300)^n) := by
  have hp (s : Fin 119 → ℤ) :
      0 ≤ inputHitProbability (by decide : 119 ≤ 512) (centeredBall 119 slackRadius) s := by
    rw [inputHitProbability_eq_fiber _ _
      (fun z hz ↦ ((mem_centeredBall slackRadius z).mp hz).1)]
    positivity
  simp_rw [raw_singleton_cumulant_contribution, abs_mul, abs_pow, abs_neg,
    abs_one, one_pow, one_mul,
    abs_of_nonneg (show (0 : ℝ) ≤ (n.factorial : ℝ) from Nat.cast_nonneg _),
    abs_of_nonneg (hp _)]
  rw [← mul_sum]
  exact mul_le_mul_of_nonneg_left (slack_inputHitProbability_power_sum_le n)
    (Nat.cast_nonneg _)

end SigabaNeo.Wall1.SlackMomentCertificate
#print axioms SigabaNeo.Wall1.RawPrefixOccupancy.inputHitProbability_eq_fiber
#print axioms SigabaNeo.Wall1.SlackMomentCertificate.slack_singleton_cumulant_sum_abs_le
