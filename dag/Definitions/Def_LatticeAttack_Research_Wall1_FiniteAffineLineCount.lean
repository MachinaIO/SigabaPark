import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic

set_option autoImplicit true

/-! Counting a finite parametrized input family by its fibers.

Taking the parameter type to be a finite field and the parametrization to be
`fun t ↦ (1-t) • y₀ + t • y₁` gives the affine-line bound. No uniqueness of
parameters or field structure is needed for this counting step.
-/
noncomputable section
namespace SigabaNeo.Wall1.FiniteAffineLineCount
open Finset
open scoped Classical
variable {α β ι : Type*} [Fintype ι]

/-- A parametrized family is a union of its input fibers, possibly overlapping. -/
theorem parametrized_filter_eq_biUnion (T : Finset α) (f : α → β) (g : ι → β) :
    (T.filter fun z ↦ ∃ t, f z = g t) =
      univ.biUnion (fun t ↦ T.filter fun z ↦ f z = g t) := by
  ext z
  simp only [mem_filter, mem_biUnion, mem_univ, true_and]
  tauto

/-- At most card ι fibers, each of cardinality at most B. -/
theorem parametrized_filter_card_le (T : Finset α) (f : α → β) (g : ι → β)
    (B : ℕ) (hB : ∀ y, (T.filter fun z ↦ f z = y).card ≤ B) :
    (T.filter fun z ↦ ∃ t, f z = g t).card ≤ Fintype.card ι * B := by
  rw [parametrized_filter_eq_biUnion]
  calc
    _ ≤ ∑ t : ι, (T.filter fun z ↦ f z = g t).card := card_biUnion_le
    _ ≤ ∑ _t : ι, B := sum_le_sum fun t _ ↦ hB (g t)
    _ = _ := by simp

/-- Real bounds on fibers can be used directly without rounding to integers. -/
theorem parametrized_filter_card_le_real (T : Finset α) (f : α → β) (g : ι → β)
    (B : ℝ) (hB : ∀ y, ((T.filter fun z ↦ f z = y).card : ℝ) ≤ B) :
    ((T.filter fun z ↦ ∃ t, f z = g t).card : ℝ) ≤ Fintype.card ι * B := by
  have hc : (T.filter fun z ↦ ∃ t, f z = g t).card ≤
      ∑ t : ι, (T.filter fun z ↦ f z = g t).card := by
    rw [parametrized_filter_eq_biUnion]
    exact card_biUnion_le
  calc
    _ ≤ ∑ t : ι, ((T.filter fun z ↦ f z = g t).card : ℝ) := by exact_mod_cast hc
    _ ≤ ∑ _t : ι, B := sum_le_sum fun t _ ↦ hB (g t)
    _ = _ := by simp

/-- Fixing the first two entries decomposes an ordered triple count exactly. -/
theorem parametrized_triples_card (T : Finset α) (f : α → β)
    (g : α → α → ι → β) :
    (((T ×ˢ T) ×ˢ T).filter fun p ↦ ∃ t, f p.2 = g p.1.1 p.1.2 t).card =
      ∑ p ∈ T ×ˢ T, (T.filter fun z ↦ ∃ t, f z = g p.1 p.2 t).card := by
  simp only [card_eq_sum_ones, sum_filter, sum_product]

/-- The third candidate lies in at most card ι fibers for each ordered pair. -/
theorem parametrized_triples_card_le (T : Finset α) (f : α → β)
    (g : α → α → ι → β) (B : ℕ)
    (hB : ∀ y, (T.filter fun z ↦ f z = y).card ≤ B) :
    (((T ×ˢ T) ×ˢ T).filter fun p ↦ ∃ t, f p.2 = g p.1.1 p.1.2 t).card ≤
      T.card^2 * Fintype.card ι * B := by
  rw [parametrized_triples_card]
  calc
    _ ≤ ∑ _p ∈ T ×ˢ T, Fintype.card ι * B :=
      sum_le_sum fun p _ ↦ parametrized_filter_card_le T f (g p.1 p.2) B hB
    _ = _ := by simp [pow_two, mul_assoc]

/-- Real-valued version suitable for geometric fiber estimates. -/
theorem parametrized_triples_card_le_real (T : Finset α) (f : α → β)
    (g : α → α → ι → β) (B : ℝ)
    (hB : ∀ y, ((T.filter fun z ↦ f z = y).card : ℝ) ≤ B) :
    ((((T ×ˢ T) ×ˢ T).filter fun p ↦ ∃ t, f p.2 = g p.1.1 p.1.2 t).card : ℝ) ≤
      (T.card : ℝ)^2 * Fintype.card ι * B := by
  rw [parametrized_triples_card, Nat.cast_sum]
  calc
    _ ≤ ∑ _p ∈ T ×ˢ T, (Fintype.card ι : ℝ) * B :=
      sum_le_sum fun p _ ↦ parametrized_filter_card_le_real T f (g p.1 p.2) B hB
    _ = _ := by simp [pow_two, mul_assoc]

end SigabaNeo.Wall1.FiniteAffineLineCount
#print axioms SigabaNeo.Wall1.FiniteAffineLineCount.parametrized_filter_card_le
#print axioms SigabaNeo.Wall1.FiniteAffineLineCount.parametrized_filter_card_le_real
#print axioms SigabaNeo.Wall1.FiniteAffineLineCount.parametrized_triples_card_le
#print axioms SigabaNeo.Wall1.FiniteAffineLineCount.parametrized_triples_card_le_real
