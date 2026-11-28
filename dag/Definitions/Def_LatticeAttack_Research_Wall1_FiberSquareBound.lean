import Definitions.Def_LatticeAttack_Research_Wall1_CandidateInputPairs

set_option autoImplicit true

/-! A finite fiber-square bound that retains the actual total candidate count. -/
namespace SigabaNeo.Wall1.CandidateInputPairs
open Finset

/-- Bounding every fiber by B bounds its square sum by B times the total size. -/
theorem inputSquareSum_le_max_mul_card {α β : Type*} [DecidableEq β]
    (T : Finset α) (f : α → β) (B : ℝ)
    (hB : ∀ s ∈ T.image f, ((T.filter fun z ↦ f z = s).card : ℝ) ≤ B) :
    (inputSquareSum T f : ℝ) ≤ B * T.card := by
  have hsum : (∑ s ∈ T.image f, ((T.filter fun z ↦ f z = s).card : ℝ)) = T.card := by
    have h := card_eq_sum_card_fiberwise
      (show (T : Set α).MapsTo f (T.image f) from fun z hz ↦ mem_image_of_mem f hz)
    exact_mod_cast h.symm
  unfold inputSquareSum
  push_cast
  calc
    _ ≤ ∑ s ∈ T.image f, B * ((T.filter fun z ↦ f z = s).card : ℝ) := by
      apply sum_le_sum
      intro s hs
      rw [pow_two]
      exact mul_le_mul_of_nonneg_right (hB s hs) (Nat.cast_nonneg _)
    _ = _ := by rw [← mul_sum, hsum]

end SigabaNeo.Wall1.CandidateInputPairs
#print axioms SigabaNeo.Wall1.CandidateInputPairs.inputSquareSum_le_max_mul_card
