import Definitions.Def_LatticeAttack_Research_Wall1_AffineGraphMoments
import Definitions.Def_LatticeAttack_Research_Wall1_DualMinimumExit

set_option autoImplicit true

/-! Uniform prefix averaging for arbitrary real observables, without conditioning. -/
noncomputable section
namespace SigabaNeo.Wall1.DualExit
open Finset QaryMembership AffineGraphMoments
open scoped Classical

/-- Restricting a uniform design preserves the average of every real observable. -/
theorem prefix_average {m n K q : ℕ} [Fact q.Prime] (hk : n ≤ K)
    (f : Design m n q → ℝ) :
    average (fun A : Design m K q ↦ f (designPrefix hk A)) = average f := by
  have expand (A : Design m K q) :
      f (designPrefix hk A) =
        ∑ B : Design m n q, (if designPrefix hk A = B then (1 : ℝ) else 0) * f B := by
    simp
  have fiber (B : Design m n q) :
      (∑ A : Design m K q, if designPrefix hk A = B then (1 : ℝ) else 0) /
          Fintype.card (Design m K q) =
        1 / (Fintype.card (Design m n q) : ℝ) := by
    have h := prefix_probability hk (fun C : Design m n q ↦ C = B)
    have hs : designs (fun C : Design m n q ↦ C = B) = {B} := by
      ext C
      simp [designs]
    simp only [probability, hs, card_singleton, Nat.cast_one] at h
    convert h using 1
    simp only [sum_boole, designs]
    congr 1
    apply congrArg (fun k : ℕ ↦ (k : ℝ))
    apply congrArg Finset.card
    ext A
    simp only [mem_filter, mem_univ, true_and]
  unfold average
  simp_rw [expand]
  rw [sum_comm, sum_div]
  simp_rw [← sum_mul, mul_div_right_comm, fiber]
  rw [← mul_sum]
  ring

end SigabaNeo.Wall1.DualExit

#print axioms SigabaNeo.Wall1.DualExit.prefix_average
