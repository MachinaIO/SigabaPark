import Definitions.Def_LatticeAttack_Research_Wall1_ExactSupportReconstruction
import Definitions.Def_LatticeAttack_Research_Wall1_RawSeriesAverage

set_option autoImplicit true

/-! Exact-support expansion of the actual raw factorial cumulants. -/
noncomputable section
namespace SigabaNeo.Wall1.RawPrefixOccupancy
open Finset PowerSeries ControlledPlane TerminalProjection FactorialMomentTransfer
open RankAdditiveSeries ExactSupportReconstruction
open scoped Classical

def rawInputLogCoeff {k : ℕ} (hk : k ≤ 512) (T : Finset (Candidate k))
    (n : ℕ) (S : Finset (Fin k → ℤ)) : ℝ :=
  coeff n (logOf (seriesAverage (fun p : Sample × Column ↦
    ∏ s ∈ S, if inputHit hk T p.1 p.2 s then (1 + X : PowerSeries ℝ) else 1)))

def rawExactSupport {k : ℕ} (hk : k ≤ 512) (T : Finset (Candidate k))
    (n : ℕ) (S : Finset (Fin k → ℤ)) : ℝ :=
  exactSupport (rawInputLogCoeff hk T n) S

theorem raw_factorialCumulant_eq_support_sum {k : ℕ} (hk : k ≤ 512)
    (T : Finset (Candidate k))
    (hT : ∀ z ∈ T, ∀ i, -1664 ≤ z.1 i ∧ z.1 i ≤ 1664) (n : ℕ) :
    factorialCumulant (factorialAverage (rawCount hk T)) n =
      (n.factorial : ℝ) * ∑ S ∈ (T.image Prod.snd).powerset, rawExactSupport hk T n S := by
  simp only [rawExactSupport, sum_exactSupport]
  unfold factorialCumulant rawInputLogCoeff
  rw [raw_factorial_series_eq_seriesAverage hk T hT]

/-- Retaining only supports with nonzero contributions is exact, at every order. -/
theorem raw_factorialCumulant_eq_retained_sum {k : ℕ} (hk : k ≤ 512)
    (T : Finset (Candidate k))
    (hT : ∀ z ∈ T, ∀ i, -1664 ≤ z.1 i ∧ z.1 i ≤ 1664) (n : ℕ)
    (P : Finset (Fin k → ℤ) → Prop) [DecidablePred P]
    (hz : ∀ S ∈ (T.image Prod.snd).powerset, ¬ P S → rawExactSupport hk T n S = 0) :
    factorialCumulant (factorialAverage (rawCount hk T)) n =
      (n.factorial : ℝ) *
        ∑ S ∈ (T.image Prod.snd).powerset.filter P, rawExactSupport hk T n S := by
  rw [raw_factorialCumulant_eq_support_sum hk T hT]
  congr 1
  exact (sum_retained_exactSupport (rawInputLogCoeff hk T n)
    (T.image Prod.snd) P hz).trans (sum_exactSupport _ _).symm |>.symm

end SigabaNeo.Wall1.RawPrefixOccupancy
#print axioms SigabaNeo.Wall1.RawPrefixOccupancy.raw_factorialCumulant_eq_support_sum
#print axioms SigabaNeo.Wall1.RawPrefixOccupancy.raw_factorialCumulant_eq_retained_sum
