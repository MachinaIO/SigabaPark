import Definitions.Def_LatticeAttack_Research_Wall1_RawDistinctInputMoments
import Definitions.Def_LatticeAttack_Research_Wall1_CenteredInputReduction
import Definitions.Def_LatticeAttack_Research_Wall1_AffineQuadrupleRank

set_option autoImplicit true

/-! Exact fourth factorial moment with all rank-two and rank-three exceptions retained. -/
noncomputable section
namespace SigabaNeo.Wall1.RawPrefixOccupancy
open Finset ControlledPlane FactorialMomentTransfer AffineGraphMoments OrderedFiberTuples
open scoped Classical
local instance : Fact (Nat.Prime 3329) := ⟨by norm_num⟩

/-- Ordered quadruples with pairwise distinct integer input blocks. -/
def distinctInputQuadruples {k : ℕ} (T : Finset (Candidate k)) :
    Finset (orderedTuples T 4) :=
  univ.filter fun e ↦ Function.Injective (fun i ↦ (e i).val.2)

/-- Distinct-input raw quadruples of a specified augmented rank. -/
def rawRankQuadruples {k : ℕ} (T : Finset (Candidate k)) (r : ℕ) :
    Finset (orderedTuples T 4) :=
  (distinctInputQuadruples T).filter fun e ↦
    (inputRows (fun i ↦ rawAffinePoint (e i).val)).rank = r

/-- Rank-r raw quadruples with consistent output constraints. -/
def rawCompatibleRankQuadruples {k : ℕ} (T : Finset (Candidate k)) (r : ℕ) :
    Finset (orderedTuples T 4) :=
  (rawRankQuadruples T r).filter fun e ↦ ∀ i,
    outputRows (fun j ↦ rawAffinePoint (e j).val) i ∈
      LinearMap.range (inputRows (fun j ↦ rawAffinePoint (e j).val)).mulVecLin

lemma raw_quadruple_inputs_ne {k : ℕ} (T : Finset (Candidate k))
    (hT : ∀ z ∈ T, ∀ i, -1664 ≤ z.2 i ∧ z.2 i ≤ 1664)
    (e : orderedTuples T 4) (he : e ∈ distinctInputQuadruples T) :
    (rawAffinePoint (e 0).val).2 ≠ (rawAffinePoint (e 1).val).2 := by
  intro hin
  have hi := (mem_filter.mp he).2
  have heq : (e 0).val.2 = (e 1).val.2 :=
    centered_reduce_injective _ _ (hT _ (e 0).property) (hT _ (e 1).property) hin
  exact (by decide : (0 : Fin 4) ≠ 1) (hi heq)

/-- The fourth actual factorial moment is an exact finite rank-count expression.
The distinct-input count is kept explicit for a later combinatorial expansion. -/
theorem raw_fourth_factorial_exact {k : ℕ} (hk : k ≤ 512)
    (T : Finset (Candidate k))
    (hout : ∀ z ∈ T, ∀ i, -1664 ≤ z.1 i ∧ z.1 i ≤ 1664)
    (hin : ∀ z ∈ T, ∀ i, -1664 ≤ z.2 i ∧ z.2 i ≤ 1664) :
    factorialAverage (rawCount hk T) 4 =
      (((distinctInputQuadruples T).card : ℝ) - (rawRankQuadruples T 2).card -
        (rawRankQuadruples T 3).card) / (3329 : ℝ)^1600 +
      (rawCompatibleRankQuadruples T 3).card / (3329 : ℝ)^1200 +
      (rawCompatibleRankQuadruples T 2).card / (3329 : ℝ)^800 := by
  rw [raw_factorial_rank_sum_distinct_inputs hk T hout]
  have hr := sum_rankWeight_quadruples (distinctInputQuadruples T)
    (fun e i ↦ rawAffinePoint (e i).val) (raw_quadruple_inputs_ne T hin)
  have hB (r : ℕ) : AffineGraphMoments.compatibleRankQuadruples (distinctInputQuadruples T)
      (fun e i ↦ rawAffinePoint (e i).val) r = rawCompatibleRankQuadruples T r := by
    unfold rawCompatibleRankQuadruples rawRankQuadruples AffineGraphMoments.compatibleRankQuadruples
    rw [filter_filter]
  rw [hB 3, hB 2] at hr
  exact hr

end SigabaNeo.Wall1.RawPrefixOccupancy
#print axioms SigabaNeo.Wall1.RawPrefixOccupancy.raw_fourth_factorial_exact
