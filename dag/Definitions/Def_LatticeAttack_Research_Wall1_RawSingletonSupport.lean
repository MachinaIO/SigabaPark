import Definitions.Def_LatticeAttack_Research_Wall1_BernoulliLogSeries

set_option autoImplicit true

/-! Exact repeated-single-input contribution to every positive-order raw cumulant. -/
noncomputable section
namespace SigabaNeo.Wall1.RawPrefixOccupancy
open Finset PowerSeries ControlledPlane TerminalProjection FactorialMomentTransfer
open RankAdditiveSeries ExactSupportReconstruction BernoulliLogSeries AffineGraphMoments
open scoped Classical

def inputHitProbability {k : ℕ} (hk : k ≤ 512) (T : Finset (Candidate k))
    (s : Fin k → ℤ) : ℝ :=
  average (fun p : Sample × Column ↦ if inputHit hk T p.1 p.2 s then 1 else 0)

theorem rawInputLogCoeff_empty {k : ℕ} (hk : k ≤ 512)
    (T : Finset (Candidate k)) (n : ℕ) : rawInputLogCoeff hk T n ∅ = 0 := by
  simp [rawInputLogCoeff, seriesAverage_const, logOf_eq]

theorem rawExactSupport_empty {k : ℕ} (hk : k ≤ 512)
    (T : Finset (Candidate k)) (n : ℕ) : rawExactSupport hk T n ∅ = 0 := by
  simp [rawExactSupport, exactSupport, rawInputLogCoeff_empty]

theorem rawExactSupport_singleton {k : ℕ} (hk : k ≤ 512)
    (T : Finset (Candidate k)) (n : ℕ) (s : Fin k → ℤ) :
    rawExactSupport hk T (n+1) {s} =
      (inputHitProbability hk T s)^(n+1) * ((-1 : ℝ)^(n+2) / (n+1)) := by
  have he : rawExactSupport hk T (n+1) {s} = rawInputLogCoeff hk T (n+1) {s} := by
    simpa [rawExactSupport, exactSupport, rawInputLogCoeff_empty] using
      exactSupport_insert (rawInputLogCoeff hk T (n+1)) ∅ s (notMem_empty s)
  rw [he]
  simpa only [rawInputLogCoeff, prod_singleton, inputHitProbability] using
    indicator_log_coeff (fun p : Sample × Column ↦ inputHit hk T p.1 p.2 s) n

theorem raw_singleton_cumulant_contribution {k : ℕ} (hk : k ≤ 512)
    (T : Finset (Candidate k)) (n : ℕ) (s : Fin k → ℤ) :
    ((n+1).factorial : ℝ) * rawExactSupport hk T (n+1) {s} =
      (-1 : ℝ)^(n+2) * (n.factorial : ℝ) * (inputHitProbability hk T s)^(n+1) := by
  rw [rawExactSupport_singleton, Nat.factorial_succ, Nat.cast_mul]
  have hn : (n+1 : ℝ) ≠ 0 := by positivity
  push_cast
  field_simp

end SigabaNeo.Wall1.RawPrefixOccupancy
#print axioms SigabaNeo.Wall1.RawPrefixOccupancy.rawExactSupport_empty
#print axioms SigabaNeo.Wall1.RawPrefixOccupancy.raw_singleton_cumulant_contribution
