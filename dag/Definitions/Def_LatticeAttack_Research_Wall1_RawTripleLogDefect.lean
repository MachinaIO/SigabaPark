import Definitions.Def_LatticeAttack_Research_Wall1_TripleSupportAlgebra
import Definitions.Def_LatticeAttack_Research_Wall1_RawPairHitProbability

set_option autoImplicit true

/-! Identify actual three-input exact supports with the cubic log-defect series. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SigabaNeo.Wall1.RawPrefixOccupancy
open Finset PowerSeries ControlledPlane TerminalProjection RankAdditiveSeries
open ExactSupportReconstruction BernoulliLogSeries TripleHitSeries CubicLogDefect
open scoped Classical

def rawTripleLogDefect {k : ℕ} (hk : k ≤ 512) (T : Finset (Candidate k))
    (s t u : Fin k → ℤ) : PowerSeries ℝ :=
  logDefect
    (inputHitProbability hk T s + inputHitProbability hk T t + inputHitProbability hk T u)
    (inputHitProbability hk T s * inputHitProbability hk T t +
      inputHitProbability hk T s * inputHitProbability hk T u +
      inputHitProbability hk T t * inputHitProbability hk T u)
    (inputHitProbability hk T s * inputHitProbability hk T t * inputHitProbability hk T u)
    (eventProbability (fun p : Sample × Column ↦
      inputHit hk T p.1 p.2 s ∧ inputHit hk T p.1 p.2 t ∧ inputHit hk T p.1 p.2 u) -
      inputHitProbability hk T s * inputHitProbability hk T t * inputHitProbability hk T u)

lemma rawInputLogCoeff_singleton_series {k : ℕ} (hk : k ≤ 512)
    (T : Finset (Candidate k)) (s : Fin k → ℤ) (n : ℕ) :
    rawInputLogCoeff hk T n {s} =
      coeff n (logOf (1+C (inputHitProbability hk T s)*X)) := by
  simp only [rawInputLogCoeff, prod_singleton, seriesAverage_indicator, smul_eq_C_mul,
    inputHitProbability]

theorem rawExactSupport_triple_eq_logDefect {k : ℕ} (hk : k ≤ 512)
    (T : Finset (Candidate k)) (s t u : Fin k → ℤ)
    (hs : ∀ i, -1664 ≤ s i ∧ s i ≤ 1664)
    (ht : ∀ i, -1664 ≤ t i ∧ t i ≤ 1664)
    (hu : ∀ i, -1664 ≤ u i ∧ u i ≤ 1664)
    (hst : s ≠ t) (hsu : s ≠ u) (htu : t ≠ u) (n : ℕ) :
    rawExactSupport hk T n {s,t,u} = coeff n (rawTripleLogDefect hk T s t u) := by
  have hsplit := exactSupport_triple_of_pair_zero (rawInputLogCoeff hk T n) s t u
    hst hsu htu (rawInputLogCoeff_empty hk T n)
    (rawExactSupport_centered_pair_zero hk T s t hs ht hst n)
    (rawExactSupport_centered_pair_zero hk T s u hs hu hsu n)
    (rawExactSupport_centered_pair_zero hk T t u ht hu htu n)
  change rawExactSupport hk T n {s,t,u} = _ at hsplit
  rw [hsplit]
  have htriple : rawInputLogCoeff hk T n {s,t,u} =
      coeff n (logOf (tripleSeries (fun p : Sample × Column ↦ inputHit hk T p.1 p.2 s)
        (fun p ↦ inputHit hk T p.1 p.2 t) (fun p ↦ inputHit hk T p.1 p.2 u))) := by
    simp [rawInputLogCoeff, tripleSeries, hst, hsu, htu, mul_assoc]
  rw [htriple, raw_tripleSeries_eq_perturbed hk T s t u hs ht hu hst hsu htu]
  simp only [rawInputLogCoeff_singleton_series, rawTripleLogDefect,
    logDefect_eq_triple_correction, map_sub, map_add]
  ring

end SigabaNeo.Wall1.RawPrefixOccupancy
#print axioms SigabaNeo.Wall1.RawPrefixOccupancy.rawExactSupport_triple_eq_logDefect
