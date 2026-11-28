import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

set_option autoImplicit true

/-! A finite exponential counting bound for coordinatewise energies.

The energy need not be nonnegative. A nonnegative tilting parameter and an
upper bound on the total energy of each counted tuple suffice. The full finite
partition sum factorizes exactly; no probabilistic independence is assumed.
-/
noncomputable section
namespace SigabaNeo.Wall1.FiniteGaussianChernoff
open Finset
open scoped Classical
variable {α : Type*} [Fintype α]

/-- The exponential partition sum over all tuples factorizes by coordinate. -/
theorem sum_exp_total_energy (N : ℕ) (E : α → ℝ) (β : ℝ) :
    (∑ x : Fin N → α, Real.exp (-β * ∑ i, E (x i))) =
      (∑ a : α, Real.exp (-β * E a))^N := by
  rw [Fintype.sum_pow]
  apply sum_congr rfl
  intro x _
  rw [← Real.exp_sum]
  congr 1
  rw [mul_sum]

/-- A finite tuple family with total energy at most L obeys a Chernoff count bound. -/
theorem card_le_exp_partition (N : ℕ) (E : α → ℝ)
    (S : Finset (Fin N → α)) (L β : ℝ) (hβ : 0 ≤ β)
    (hE : ∀ x ∈ S, (∑ i, E (x i)) ≤ L) :
    (S.card : ℝ) ≤ Real.exp (β * L) * (∑ a : α, Real.exp (-β * E a))^N := by
  have hpoint (x : Fin N → α) (hx : x ∈ S) :
      1 ≤ Real.exp (β * L) * Real.exp (-β * ∑ i, E (x i)) := by
    rw [← Real.exp_add, Real.one_le_exp_iff]
    nlinarith [mul_nonneg hβ (sub_nonneg.mpr (hE x hx))]
  calc
    (S.card : ℝ) = ∑ _x ∈ S, (1 : ℝ) := by simp
    _ ≤ ∑ x ∈ S, Real.exp (β * L) * Real.exp (-β * ∑ i, E (x i)) :=
      sum_le_sum hpoint
    _ = Real.exp (β * L) * ∑ x ∈ S, Real.exp (-β * ∑ i, E (x i)) := by
      rw [mul_sum]
    _ ≤ Real.exp (β * L) * ∑ x : Fin N → α, Real.exp (-β * ∑ i, E (x i)) := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      apply sum_le_sum_of_subset_of_nonneg (subset_univ S)
      intro x _ _
      exact (Real.exp_pos _).le
    _ = _ := by rw [sum_exp_total_energy]

end SigabaNeo.Wall1.FiniteGaussianChernoff
#print axioms SigabaNeo.Wall1.FiniteGaussianChernoff.sum_exp_total_energy
#print axioms SigabaNeo.Wall1.FiniteGaussianChernoff.card_le_exp_partition
