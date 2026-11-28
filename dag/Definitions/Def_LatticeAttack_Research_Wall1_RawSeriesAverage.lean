import Definitions.Def_LatticeAttack_Research_Wall1_RankAdditiveSeries
import Definitions.Def_LatticeAttack_Research_Wall1_RawInputIndicators

set_option autoImplicit true

/-! Identify the actual factorial generating series with the uniform series average. -/
noncomputable section
namespace SigabaNeo.Wall1.RankAdditiveSeries
open Finset PowerSeries AffineGraphMoments FactorialMomentTransfer

theorem seriesAverage_eq_sum {Ω : Type*} [Fintype Ω] (F : Ω → PowerSeries ℝ) :
    seriesAverage F = (Fintype.card Ω : ℝ)⁻¹ • ∑ x, F x := by
  ext n
  simp only [coeff_seriesAverage, map_smul, map_sum, smul_eq_mul, average]
  rw [div_eq_mul_inv, mul_comm]

theorem normalizedMomentSeries_eq_seriesAverage {Ω α : Type*}
    [Fintype Ω] [Fintype α] (n : Ω → α → ℕ) :
    normalizedMomentSeries (factorialAverage n) =
      seriesAverage (fun p : Ω × α ↦ (1 + X : PowerSeries ℝ)^(n p.1 p.2)) := by
  rw [normalizedMomentSeries_factorialAverage, seriesAverage_eq_sum]
  simp only [Fintype.card_prod, Nat.cast_mul, Fintype.sum_prod_type]

end SigabaNeo.Wall1.RankAdditiveSeries

namespace SigabaNeo.Wall1.RawPrefixOccupancy
open Finset PowerSeries ControlledPlane TerminalProjection FactorialMomentTransfer
open RankAdditiveSeries
open scoped Classical

/-- This is the joint uniform law on the actual matrix and target column; no
independence between input hits is assumed. -/
theorem raw_factorial_series_eq_seriesAverage {k : ℕ} (hk : k ≤ 512)
    (T : Finset (Candidate k))
    (hT : ∀ z ∈ T, ∀ i, -1664 ≤ z.1 i ∧ z.1 i ≤ 1664) :
    normalizedMomentSeries (factorialAverage (rawCount hk T)) =
      seriesAverage (fun p : Sample × Column ↦
        ∏ s ∈ T.image Prod.snd,
          if inputHit hk T p.1 p.2 s then (1 + X : PowerSeries ℝ) else 1) := by
  rw [normalizedMomentSeries_eq_seriesAverage]
  congr 1
  funext p
  exact raw_generating_product hk T hT p.1 p.2

end SigabaNeo.Wall1.RawPrefixOccupancy
#print axioms SigabaNeo.Wall1.RawPrefixOccupancy.raw_factorial_series_eq_seriesAverage
