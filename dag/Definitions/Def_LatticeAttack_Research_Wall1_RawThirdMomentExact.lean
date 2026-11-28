import Definitions.Def_LatticeAttack_Research_Wall1_RawDistinctInputMoments
import Definitions.Def_LatticeAttack_Research_Wall1_CandidateInputTriples
import Definitions.Def_LatticeAttack_Research_Wall1_AffineTripleRank

set_option autoImplicit true

/-! Exact third factorial moment, separating the exceptional rank-two triples. -/
noncomputable section
namespace SigabaNeo.Wall1.RawPrefixOccupancy
open Finset ControlledPlane FactorialMomentTransfer AffineGraphMoments OrderedFiberTuples
open CandidateInputPairs
open scoped Classical
local instance : Fact (Nat.Prime 3329) := ⟨by norm_num⟩

/-- Ordered triples whose integer input blocks are distinct. -/
def distinctInputTriples {k : ℕ} (T : Finset (Candidate k)) :
    Finset (orderedTuples T 3) :=
  univ.filter fun e ↦ Function.Injective (fun i ↦ (e i).val.2)

/-- The exceptional triples of augmented-input rank two. -/
def rankTwoTriples {k : ℕ} (T : Finset (Candidate k)) : Finset (orderedTuples T 3) :=
  (distinctInputTriples T).filter fun e ↦
    (inputRows (fun i ↦ rawAffinePoint (e i).val)).rank = 2

/-- Rank-two triples whose outputs satisfy the same linear constraints. -/
def compatibleRankTwoTriples {k : ℕ} (T : Finset (Candidate k)) :
    Finset (orderedTuples T 3) :=
  (rankTwoTriples T).filter fun e ↦ ∀ i,
    outputRows (fun j ↦ rawAffinePoint (e j).val) i ∈
      LinearMap.range (inputRows (fun j ↦ rawAffinePoint (e j).val)).mulVecLin

lemma raw_triple_inputs_ne {k : ℕ} (T : Finset (Candidate k))
    (hT : ∀ z ∈ T, ∀ i, -1664 ≤ z.2 i ∧ z.2 i ≤ 1664)
    (e : orderedTuples T 3) (he : e ∈ distinctInputTriples T) :
    (rawAffinePoint (e 0).val).2 ≠ (rawAffinePoint (e 1).val).2 := by
  intro hin
  have hi := (mem_filter.mp he).2
  have heq : (e 0).val.2 = (e 1).val.2 := by
    funext i
    apply centered_intCast_injective (hT _ (e 0).property i) (hT _ (e 1).property i)
    exact congrFun hin i
  have h01 := hi heq
  exact (by decide : (0 : Fin 3) ≠ 1) h01

/-- Exact third factorial moment for a fixed centered family. Only rank-two
counts remain; no estimate on their sizes is assumed. -/
theorem raw_third_factorial_exact {k : ℕ} (hk : k ≤ 512)
    (T : Finset (Candidate k))
    (hout : ∀ z ∈ T, ∀ i, -1664 ≤ z.1 i ∧ z.1 i ≤ 1664)
    (hin : ∀ z ∈ T, ∀ i, -1664 ≤ z.2 i ∧ z.2 i ≤ 1664) :
    factorialAverage (rawCount hk T) 3 =
      ((T.card : ℝ)^3 - 3 * T.card * inputSquareSum T Prod.snd +
        2 * inputCubeSum T Prod.snd - (rankTwoTriples T).card) / (3329 : ℝ)^1200 +
        (compatibleRankTwoTriples T).card / (3329 : ℝ)^800 := by
  rw [raw_factorial_rank_sum_distinct_inputs hk T hout]
  have hr := sum_rankWeight_triples (distinctInputTriples T)
    (fun e i ↦ rawAffinePoint (e i).val) (raw_triple_inputs_ne T hin)
  have hc := ordered_distinct_input_triples_card_real T Prod.snd
  change ((distinctInputTriples T).card : ℝ) = _ at hc
  rw [hc] at hr
  have hB : AffineGraphMoments.compatibleRankTwoTriples (distinctInputTriples T)
      (fun e i ↦ rawAffinePoint (e i).val) = compatibleRankTwoTriples T := by
    unfold compatibleRankTwoTriples rankTwoTriples AffineGraphMoments.compatibleRankTwoTriples
    rw [filter_filter]
  rw [hB] at hr
  exact hr

end SigabaNeo.Wall1.RawPrefixOccupancy
#print axioms SigabaNeo.Wall1.RawPrefixOccupancy.raw_third_factorial_exact
