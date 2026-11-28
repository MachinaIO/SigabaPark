import Definitions.Def_LatticeAttack_Research_Wall1_RawFactorialRankSum
import Definitions.Def_LatticeAttack_Research_Wall1_RawPairCollision

set_option autoImplicit true

/-! Only tuples with distinct inputs contribute to centered raw factorial moments. -/
noncomputable section
namespace SigabaNeo.Wall1.AffineGraphMoments
open Matrix
open scoped Classical

/-- Equal inputs with different outputs make an affine tuple inconsistent. -/
theorem rankWeight_eq_zero_of_repeated_input {q m n h : ℕ} [Fact q.Prime]
    (z : Fin h → Point m n q) (a b : Fin h)
    (hin : (z a).2 = (z b).2) (hout : (z a).1 ≠ (z b).1) :
    rankWeight z = 0 := by
  have hc : ¬ ∀ i, outputRows z i ∈ LinearMap.range (inputRows z).mulVecLin := by
    intro hc
    apply hout
    funext i
    obtain ⟨v, hv⟩ := hc i
    have ha := congrFun hv a
    have hb := congrFun hv b
    change (inputRows z).mulVec v a = (z a).1 i at ha
    change (inputRows z).mulVec v b = (z b).1 i at hb
    have he : (inputRows z).mulVec v a = (inputRows z).mulVec v b := by
      simp only [mulVec, inputRows, hin]
    exact ha.symm.trans (he.trans hb)
  simp only [rankWeight, ite_eq_right hc]

end SigabaNeo.Wall1.AffineGraphMoments

namespace SigabaNeo.Wall1.RawPrefixOccupancy
open Finset ControlledPlane QaryMembership AffineGraphMoments OrderedFiberTuples
open FactorialMomentTransfer
open scoped Classical
local instance : Fact (Nat.Prime 3329) := ⟨by norm_num⟩

/-- Repeated integer inputs have zero rank weight in a distinct-candidate tuple,
provided the output representatives are centered. -/
theorem raw_rankWeight_zero_of_not_injective {k h : ℕ}
    (T : Finset (Candidate k))
    (hT : ∀ z ∈ T, ∀ i, -1664 ≤ z.1 i ∧ z.1 i ≤ 1664)
    (e : orderedTuples T h) (hne : ¬ Function.Injective (fun i ↦ (e i).val.2)) :
    rankWeight (fun i ↦ rawAffinePoint (e i).val) = 0 := by
  obtain ⟨a, b, hin, hab⟩ := Function.not_injective_iff.mp hne
  apply rankWeight_eq_zero_of_repeated_input _ a b
  · change reduce 3329 (e a).val.2 = reduce 3329 (e b).val.2
    rw [hin]
  · intro hout
    apply hab
    apply e.injective
    apply Subtype.ext
    apply Prod.ext _ hin
    funext i
    apply centered_intCast_injective (hT _ (e a).property i) (hT _ (e b).property i)
    exact congrFun hout i

/-- Exact factorial rank sum restricted to distinct input blocks; no probability
is lost by this restriction, and the empty tuple is retained. -/
theorem raw_factorial_rank_sum_distinct_inputs {k : ℕ} (hk : k ≤ 512)
    (T : Finset (Candidate k))
    (hT : ∀ z ∈ T, ∀ i, -1664 ≤ z.1 i ∧ z.1 i ≤ 1664) (h : ℕ) :
    factorialAverage (rawCount hk T) h =
      ∑ e ∈ (univ : Finset (orderedTuples T h)).filter
        (fun e ↦ Function.Injective (fun i ↦ (e i).val.2)),
        rankWeight (fun i ↦ rawAffinePoint (e i).val) := by
  rw [raw_factorial_rank_sum]
  symm
  apply sum_subset (filter_subset _ _)
  intro e _ he
  apply raw_rankWeight_zero_of_not_injective T hT e
  simpa only [mem_filter, mem_univ, true_and] using he

end SigabaNeo.Wall1.RawPrefixOccupancy
#print axioms SigabaNeo.Wall1.AffineGraphMoments.rankWeight_eq_zero_of_repeated_input
#print axioms SigabaNeo.Wall1.RawPrefixOccupancy.raw_factorial_rank_sum_distinct_inputs
