import Definitions.Def_LatticeAttack_Research_Wall1_BernoulliCoefficientMajorant

set_option autoImplicit true

noncomputable section
namespace SigabaNeo.Wall1.CoefficientMajorant
open PowerSeries Finset

def AggregateMajorized {α : Type*} (S : Finset α) (F : α → PowerSeries ℝ)
    (H : PowerSeries ℝ) : Prop := ∀ n, ∑ s ∈ S, |coeff n (F s)| ≤ coeff n H

namespace AggregateMajorized
variable {α : Type*} {S : Finset α} {F G : α → PowerSeries ℝ} {H K : PowerSeries ℝ}

theorem add (hf : AggregateMajorized S F H) (hg : AggregateMajorized S G K) :
    AggregateMajorized S (fun s ↦ F s + G s) (H+K) := by
  intro n
  simp only [map_add]
  calc
    _ ≤ ∑ s ∈ S, (|coeff n (F s)| + |coeff n (G s)|) :=
      sum_le_sum (fun _ _ ↦ abs_add_le _ _)
    _ = _ := sum_add_distrib
    _ ≤ _ := add_le_add (hf n) (hg n)

theorem sub (hf : AggregateMajorized S F H) (hg : AggregateMajorized S G K) :
    AggregateMajorized S (fun s ↦ F s - G s) (H+K) := by
  intro n
  simp only [map_sub, map_add]
  calc
    _ ≤ ∑ s ∈ S, (|coeff n (F s)| + |coeff n (G s)|) :=
      sum_le_sum (fun _ _ ↦ abs_sub _ _)
    _ = _ := sum_add_distrib
    _ ≤ _ := add_le_add (hf n) (hg n)

theorem shift (hf : AggregateMajorized S F H) (k : ℕ) :
    AggregateMajorized S (fun s ↦ X^k * F s) (X^k * H) := by
  intro n
  by_cases h : k ≤ n
  · simpa only [coeff_X_pow_mul', ite_eq_left h] using hf (n-k)
  · simp only [coeff_X_pow_mul', ite_eq_right h, abs_zero, sum_const_zero, le_refl]

end AggregateMajorized
end SigabaNeo.Wall1.CoefficientMajorant
#print axioms SigabaNeo.Wall1.CoefficientMajorant.AggregateMajorized.shift
