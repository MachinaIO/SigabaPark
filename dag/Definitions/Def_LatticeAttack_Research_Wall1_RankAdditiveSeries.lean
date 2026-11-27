import Definitions.Def_LatticeAttack_Research_Wall1_RankAdditiveAverage
import Mathlib.RingTheory.PowerSeries.Basic

set_option autoImplicit true

/-! Exact averaged formal-series factorization for rank-additive uniform observations. -/
noncomputable section
namespace SigabaNeo.Wall1.RankAdditiveSeries
open Finset PowerSeries AffineGraphMoments RankAdditiveAverage

/-- Formal series averaged coefficientwise over a finite uniform sample space. -/
def seriesAverage {Ω : Type*} [Fintype Ω] (F : Ω → PowerSeries ℝ) : PowerSeries ℝ :=
  PowerSeries.mk (fun n ↦ average (fun x ↦ coeff n (F x)))

lemma coeff_seriesAverage {Ω : Type*} [Fintype Ω] (F : Ω → PowerSeries ℝ) (n : ℕ) :
    coeff n (seriesAverage F) = average (fun x ↦ coeff n (F x)) := by
  exact coeff_mk n _

lemma average_finset_sum {Ω ι : Type*} [Fintype Ω] (s : Finset ι) (F : Ω → ι → ℝ) :
    average (fun x ↦ ∑ i ∈ s, F x i) = ∑ i ∈ s, average (fun x ↦ F x i) := by
  simp only [average, sum_comm (s := (univ : Finset Ω)) (t := s), sum_div]

variable {K V W U : Type*} [Field K]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
  [AddCommGroup U] [Module K U] [FiniteDimensional K W] [FiniteDimensional K U]
  [Fintype V] [Fintype W] [Fintype U]

/-- Rank additivity proves the series factorization itself, for arbitrary series-valued observables. -/
theorem seriesAverage_mul_of_rank_additive (f : V →ₗ[K] W) (g : V →ₗ[K] U)
    (hr : Module.finrank K (f.prod g).range =
      Module.finrank K f.range + Module.finrank K g.range)
    (F : W → PowerSeries ℝ) (G : U → PowerSeries ℝ) :
    seriesAverage (fun x : V ↦ F (f x)*G (g x)) =
      seriesAverage (fun x : V ↦ F (f x)) * seriesAverage (fun x : V ↦ G (g x)) := by
  apply PowerSeries.ext
  intro n
  simp only [coeff_seriesAverage, coeff_mul]
  rw [average_finset_sum]
  apply sum_congr rfl
  intro p _
  exact average_mul_of_rank_additive f g hr (fun y ↦ coeff p.1 (F y))
    (fun z ↦ coeff p.2 (G z))

end SigabaNeo.Wall1.RankAdditiveSeries
#print axioms SigabaNeo.Wall1.RankAdditiveSeries.seriesAverage_mul_of_rank_additive
