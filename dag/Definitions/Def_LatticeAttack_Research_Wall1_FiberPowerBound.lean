import Definitions.Def_LatticeAttack_Research_Wall1_FiberSquareBound

set_option autoImplicit true

/-! All positive fiber-power sums are controlled by the maximal fiber. -/
namespace SigabaNeo.Wall1.CandidateInputPairs
open Finset

/-- Power sums include repeated candidates within a single input fiber. -/
def inputPowerSum {α β : Type*} [DecidableEq β] (T : Finset α) (f : α → β) (h : ℕ) : ℕ :=
  ∑ s ∈ T.image f, ((T.filter fun z ↦ f z = s).card)^h

theorem inputPowerSum_succ_le {α β : Type*} [DecidableEq β]
    (T : Finset α) (f : α → β) (B : ℝ)
    (hB : ∀ s ∈ T.image f, ((T.filter fun z ↦ f z = s).card : ℝ) ≤ B) (n : ℕ) :
    (inputPowerSum T f (n+1) : ℝ) ≤ B^n * T.card := by
  have hsum : (∑ s ∈ T.image f, ((T.filter fun z ↦ f z = s).card : ℝ)) = T.card := by
    have h := card_eq_sum_card_fiberwise
      (show (T : Set α).MapsTo f (T.image f) from fun z hz ↦ mem_image_of_mem f hz)
    exact_mod_cast h.symm
  unfold inputPowerSum
  push_cast
  calc
    _ ≤ ∑ s ∈ T.image f, B^n * ((T.filter fun z ↦ f z = s).card : ℝ) := by
      apply sum_le_sum
      intro s hs
      rw [pow_succ]
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (Nat.cast_nonneg _) (hB s hs) n) (Nat.cast_nonneg _)
    _ = _ := by rw [← mul_sum, hsum]

end SigabaNeo.Wall1.CandidateInputPairs
#print axioms SigabaNeo.Wall1.CandidateInputPairs.inputPowerSum_succ_le
