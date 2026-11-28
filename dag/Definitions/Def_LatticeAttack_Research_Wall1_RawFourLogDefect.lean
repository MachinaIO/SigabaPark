import Definitions.Def_LatticeAttack_Research_Wall1_FourSupportAlgebra
import Definitions.Def_LatticeAttack_Research_Wall1_RawTripleLogDefect

set_option autoImplicit true

/-! Actual four-input log correction, retaining and subtracting triple dependencies. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SigabaNeo.Wall1.RawPrefixOccupancy
open Finset PowerSeries ControlledPlane TerminalProjection RankAdditiveSeries
open ExactSupportReconstruction
open scoped Classical

def rawFourLogDefect {k : ℕ} (hk : k ≤ 512) (T : Finset (Candidate k))
    (a b c d : Fin k → ℤ) : PowerSeries ℝ :=
  logOf (seriesAverage (fun p : Sample × Column ↦
    ∏ s ∈ ({a,b,c,d} : Finset (Fin k → ℤ)),
      if inputHit hk T p.1 p.2 s then (1+X : PowerSeries ℝ) else 1)) -
    (logOf (1+C (inputHitProbability hk T a)*X) +
      logOf (1+C (inputHitProbability hk T b)*X) +
      logOf (1+C (inputHitProbability hk T c)*X) +
      logOf (1+C (inputHitProbability hk T d)*X)) -
    (rawTripleLogDefect hk T a b c + rawTripleLogDefect hk T a b d +
      rawTripleLogDefect hk T a c d + rawTripleLogDefect hk T b c d)

theorem rawExactSupport_four_eq_logDefect {k : ℕ} (hk : k ≤ 512)
    (T : Finset (Candidate k)) (a b c d : Fin k → ℤ)
    (ha : ∀ i, -1664 ≤ a i ∧ a i ≤ 1664)
    (hb : ∀ i, -1664 ≤ b i ∧ b i ≤ 1664)
    (hc : ∀ i, -1664 ≤ c i ∧ c i ≤ 1664)
    (hd : ∀ i, -1664 ≤ d i ∧ d i ≤ 1664)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) (n : ℕ) :
    rawExactSupport hk T n {a,b,c,d} = coeff n (rawFourLogDefect hk T a b c d) := by
  have he := exactSupport_four_of_pair_zero (rawInputLogCoeff hk T n) a b c d
    hab hac had hbc hbd hcd (rawInputLogCoeff_empty hk T n)
    (rawExactSupport_centered_pair_zero hk T a b ha hb hab n)
    (rawExactSupport_centered_pair_zero hk T a c ha hc hac n)
    (rawExactSupport_centered_pair_zero hk T a d ha hd had n)
    (rawExactSupport_centered_pair_zero hk T b c hb hc hbc n)
    (rawExactSupport_centered_pair_zero hk T b d hb hd hbd n)
    (rawExactSupport_centered_pair_zero hk T c d hc hd hcd n)
  change rawExactSupport hk T n {a,b,c,d} =
    rawInputLogCoeff hk T n {a,b,c,d} -
      (rawInputLogCoeff hk T n {a} + rawInputLogCoeff hk T n {b} +
        rawInputLogCoeff hk T n {c} + rawInputLogCoeff hk T n {d}) -
      (rawExactSupport hk T n {a,b,c} + rawExactSupport hk T n {a,b,d} +
        rawExactSupport hk T n {a,c,d} + rawExactSupport hk T n {b,c,d}) at he
  rw [he, rawExactSupport_triple_eq_logDefect hk T a b c ha hb hc hab hac hbc,
    rawExactSupport_triple_eq_logDefect hk T a b d ha hb hd hab had hbd,
    rawExactSupport_triple_eq_logDefect hk T a c d ha hc hd hac had hcd,
    rawExactSupport_triple_eq_logDefect hk T b c d hb hc hd hbc hbd hcd]
  simp only [rawInputLogCoeff_singleton_series, rawFourLogDefect, map_sub, map_add]
  rfl

end SigabaNeo.Wall1.RawPrefixOccupancy
#print axioms SigabaNeo.Wall1.RawPrefixOccupancy.rawExactSupport_four_eq_logDefect
