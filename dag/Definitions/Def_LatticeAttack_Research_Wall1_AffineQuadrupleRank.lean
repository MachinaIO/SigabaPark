import Definitions.Def_LatticeAttack_Research_Wall1_AffineTripleRank

set_option autoImplicit true

/-! Exact rank and compatibility decomposition for affine quadruple families. -/
noncomputable section
namespace SigabaNeo.Wall1.AffineGraphMoments
open Matrix Finset
open scoped Classical
variable {q m n : ℕ} [Fact q.Prime]

/-- Two different inputs exclude ranks zero and one in any quadruple. -/
theorem inputRows_quadruple_rank_cases (z : Fin 4 → Point m n q)
    (hne : (z 0).2 ≠ (z 1).2) :
    (inputRows z).rank = 2 ∨ (inputRows z).rank = 3 ∨ (inputRows z).rank = 4 := by
  have hlo := inputRows_rank_ge_two z 0 1 hne
  have hhi := (inputRows z).rank_le_height
  omega

/-- Rank-four quadruples are automatically consistent; lower ranks retain explicit feasibility. -/
theorem rankWeight_quadruple_cases (z : Fin 4 → Point m n q)
    (hne : (z 0).2 ≠ (z 1).2) :
    rankWeight z =
      if (inputRows z).rank = 2 then
        (if ∀ i, outputRows z i ∈ LinearMap.range (inputRows z).mulVecLin then
          1 / (q : ℝ)^(2*m) else 0)
      else if (inputRows z).rank = 3 then
        (if ∀ i, outputRows z i ∈ LinearMap.range (inputRows z).mulVecLin then
          1 / (q : ℝ)^(3*m) else 0)
      else 1 / (q : ℝ)^(4*m) := by
  rcases inputRows_quadruple_rank_cases z hne with hr | hr | hr
  · simp only [hr, ↓reduceIte, rankWeight]
  · simp only [hr, Nat.reduceEqDiff, ↓reduceIte, rankWeight]
  · rw [rankWeight_of_full_row_rank z hr]
    simp only [hr, Nat.reduceEqDiff, ↓reduceIte]

/-- Quadruples of a specified augmented-input rank. -/
def rankQuadruples {α : Type*} (S : Finset α) (z : α → Fin 4 → Point m n q)
    (r : ℕ) : Finset α := S.filter fun e ↦ (inputRows (z e)).rank = r

/-- Rank-r quadruples with consistent output constraints. -/
def compatibleRankQuadruples {α : Type*} (S : Finset α)
    (z : α → Fin 4 → Point m n q) (r : ℕ) : Finset α :=
  S.filter fun e ↦ (inputRows (z e)).rank = r ∧
    ∀ i, outputRows (z e) i ∈ LinearMap.range (inputRows (z e)).mulVecLin

/-- Every finite quadruple rank sum reduces to four exceptional-family counts.
All cardinality subtraction is over the reals, not truncated natural subtraction. -/
theorem sum_rankWeight_quadruples {α : Type*} (S : Finset α)
    (z : α → Fin 4 → Point m n q)
    (hne : ∀ e ∈ S, (z e 0).2 ≠ (z e 1).2) :
    ∑ e ∈ S, rankWeight (z e) =
      ((S.card : ℝ) - (rankQuadruples S z 2).card - (rankQuadruples S z 3).card) /
        (q : ℝ)^(4*m) +
      (compatibleRankQuadruples S z 3).card / (q : ℝ)^(3*m) +
      (compatibleRankQuadruples S z 2).card / (q : ℝ)^(2*m) := by
  have he : ∀ e ∈ S, rankWeight (z e) =
      1 / (q : ℝ)^(4*m) -
        (if (inputRows (z e)).rank = 2 then 1 / (q : ℝ)^(4*m) else 0) -
        (if (inputRows (z e)).rank = 3 then 1 / (q : ℝ)^(4*m) else 0) +
        (if (inputRows (z e)).rank = 3 ∧
          ∀ i, outputRows (z e) i ∈ LinearMap.range (inputRows (z e)).mulVecLin
          then 1 / (q : ℝ)^(3*m) else 0) +
        (if (inputRows (z e)).rank = 2 ∧
          ∀ i, outputRows (z e) i ∈ LinearMap.range (inputRows (z e)).mulVecLin
          then 1 / (q : ℝ)^(2*m) else 0) := by
    intro e he
    rw [rankWeight_quadruple_cases (z e) (hne e he)]
    split_ifs <;> simp_all
  rw [Finset.sum_congr rfl he]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_ite,
    Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul,
    rankQuadruples, compatibleRankQuadruples]
  ring

end SigabaNeo.Wall1.AffineGraphMoments
#print axioms SigabaNeo.Wall1.AffineGraphMoments.inputRows_quadruple_rank_cases
#print axioms SigabaNeo.Wall1.AffineGraphMoments.sum_rankWeight_quadruples
