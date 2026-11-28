import Definitions.Def_LatticeAttack_Research_Wall1_CandidateInputTriples
import Definitions.Def_LatticeAttack_Research_Wall1_FiberSquareBound

set_option autoImplicit true

/-! Fiber-cube bounds using the maximum fiber and the actual total size. -/
namespace SigabaNeo.Wall1.CandidateInputPairs
open Finset

/-- Cubing each fiber costs at most two factors of the maximal fiber size. -/
theorem inputCubeSum_le_max_sq_mul_card {α β : Type*} [DecidableEq β]
    (T : Finset α) (f : α → β) (B : ℝ) (hB0 : 0 ≤ B)
    (hB : ∀ s ∈ T.image f, ((T.filter fun z ↦ f z = s).card : ℝ) ≤ B) :
    (inputCubeSum T f : ℝ) ≤ B^2 * T.card := by
  have hsq := inputSquareSum_le_max_mul_card T f B hB
  have hc : (inputCubeSum T f : ℝ) ≤ B * inputSquareSum T f := by
    unfold inputCubeSum inputSquareSum
    push_cast
    rw [mul_sum]
    apply sum_le_sum
    intro s hs
    calc
      _ = ((T.filter fun z ↦ f z = s).card : ℝ) *
          ((T.filter fun z ↦ f z = s).card : ℝ)^2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (hB s hs) (sq_nonneg _)
  exact hc.trans ((mul_le_mul_of_nonneg_left hsq hB0).trans_eq (by ring))

end SigabaNeo.Wall1.CandidateInputPairs
#print axioms SigabaNeo.Wall1.CandidateInputPairs.inputCubeSum_le_max_sq_mul_card
