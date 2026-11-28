import Definitions.Def_LatticeAttack_Research_Wall1_AffineGraphMoments
import Definitions.Def_LatticeAttack_Research_Wall1_OrderedFiberTuples

set_option autoImplicit true

/-! Exact factorial moments of a fixed finite candidate family as rank-weighted
ordered distinct tuples. Distinct indices need not have distinct point images. -/
noncomputable section
namespace SigabaNeo.Wall1.AffineGraphMoments
open Finset OrderedFiberTuples QaryMembership DualExit
open scoped Classical
variable {q m n : ℕ} [Fact q.Prime] {α : Type*}

/-- Number of indices whose point is incident to the given affine graph. -/
def finiteHitCount (T : Finset α) (z : α → Point m n q)
    (A : Design m (n+1) q) : ℕ :=
  (T.filter fun i ↦ incident A (z i)).card

/-- The falling factorial counts ordered distinct indices, also at degree zero. -/
theorem finiteHitCount_descFactorial (T : Finset α) (z : α → Point m n q)
    (A : Design m (n+1) q) (h : ℕ) :
    ((finiteHitCount T z A).descFactorial h : ℝ) =
      ∑ e : orderedTuples T h, if ∀ i, incident A (z (e i)) then (1 : ℝ) else 0 := by
  have hc := allHits_card T (fun i ↦ decide (incident A (z i))) true h
  simp only [decide_eq_true_eq] at hc
  rw [finiteHitCount, ← hc]
  simp [allHits]

/-- Exact factorial moments under the original uniform affine design law.
No independence or injectivity assumption on the indexed points is required. -/
theorem factorial_moment (T : Finset α) (z : α → Point m n q) (h : ℕ) :
    average (fun A : Design m (n+1) q ↦
      ((finiteHitCount T z A).descFactorial h : ℝ)) =
      ∑ e : orderedTuples T h, rankWeight (fun i ↦ z (e i)) := by
  simp_rw [finiteHitCount_descFactorial]
  unfold average
  rw [sum_comm, sum_div]
  apply sum_congr rfl
  intro e _
  have hp := joint_probability (fun i ↦ z (e i))
  simp only [probability, designs] at hp
  convert hp using 1
  simp only [sum_boole]
  congr 1
  apply congrArg (fun k : ℕ ↦ (k : ℝ))
  apply congrArg Finset.card
  ext A
  simp only [mem_filter, mem_univ, true_and]

end SigabaNeo.Wall1.AffineGraphMoments

#print axioms SigabaNeo.Wall1.AffineGraphMoments.finiteHitCount_descFactorial
#print axioms SigabaNeo.Wall1.AffineGraphMoments.factorial_moment
