import Definitions.Def_LatticeAttack_Research_Wall1_AffineGraphMoments

set_option autoImplicit true

/-! Rank alternatives for affine triples with distinct input blocks. -/
noncomputable section
namespace SigabaNeo.Wall1.AffineGraphMoments
open Matrix
open scoped Classical
variable {q m n h : ℕ} [Fact q.Prime]

/-- Any two different inputs supply a nonsingular two-by-two augmented minor. -/
theorem inputRows_rank_ge_two (z : Fin h → Point m n q) (a b : Fin h)
    (hne : (z a).2 ≠ (z b).2) : 2 ≤ (inputRows z).rank := by
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hne
  let r : Fin 2 → Fin h := ![a, b]
  let c : Fin 2 → Fin (n+1) := ![0, j.succ]
  have hd : ((inputRows z).submatrix r c).det ≠ 0 := by
    simpa [Matrix.det_fin_two, Matrix.submatrix, inputRows, augmented, r, c] using
      (sub_ne_zero.mpr hj.symm)
  have hr := Matrix.rank_of_det_ne_zero hd
  have hm := Matrix.rank_submatrix_le (inputRows z) r c
  simpa only [hr, Fintype.card_fin] using hm

/-- A triple with two distinct inputs has augmented rank exactly two or three. -/
theorem inputRows_triple_rank_two_or_three (z : Fin 3 → Point m n q)
    (hne : (z 0).2 ≠ (z 1).2) :
    (inputRows z).rank = 2 ∨ (inputRows z).rank = 3 := by
  have hlo := inputRows_rank_ge_two z 0 1 hne
  have hhi := (inputRows z).rank_le_height
  omega

/-- Full row rank guarantees compatibility with every output tuple. -/
theorem rankWeight_of_full_row_rank (z : Fin h → Point m n q)
    (hr : (inputRows z).rank = h) : rankWeight z = 1 / (q : ℝ)^(h*m) := by
  have hs : (inputRows z).mulVec.Surjective :=
    Matrix.mulVec_surjective_iff_rank_eq_card.mpr (by simpa using hr)
  have hc : ∀ i, outputRows z i ∈ LinearMap.range (inputRows z).mulVecLin := by
    intro i
    obtain ⟨v, hv⟩ := hs (outputRows z i)
    exact ⟨v, hv⟩
  simp only [rankWeight, ite_eq_left_iff, hr]
  exact fun hn ↦ (hn hc).elim

/-- The only exceptional triple weight is a compatible rank-two system. -/
theorem rankWeight_triple_cases (z : Fin 3 → Point m n q)
    (hne : (z 0).2 ≠ (z 1).2) :
    rankWeight z =
      if (inputRows z).rank = 2 then
        (if ∀ i, outputRows z i ∈ LinearMap.range (inputRows z).mulVecLin then
          1 / (q : ℝ)^(2*m) else 0)
      else 1 / (q : ℝ)^(3*m) := by
  rcases inputRows_triple_rank_two_or_three z hne with hr | hr
  · simp only [hr, ↓reduceIte, rankWeight]
  · rw [rankWeight_of_full_row_rank z hr]
    simp only [hr, Nat.reduceEqDiff, ↓reduceIte]

/-- Rank-two members of a finite family of affine triples. -/
def rankTwoTriples {α : Type*} (S : Finset α) (z : α → Fin 3 → Point m n q) : Finset α :=
  S.filter fun e ↦ (inputRows (z e)).rank = 2

/-- The rank-two triples whose output constraints are consistent. -/
def compatibleRankTwoTriples {α : Type*} (S : Finset α)
    (z : α → Fin 3 → Point m n q) : Finset α :=
  S.filter fun e ↦ (inputRows (z e)).rank = 2 ∧
    ∀ i, outputRows (z e) i ∈ LinearMap.range (inputRows (z e)).mulVecLin

/-- Exact triple rank sum expressed by two exceptional-family cardinalities.
The subtraction is in the reals, so this formula has no truncated subtraction. -/
theorem sum_rankWeight_triples {α : Type*} (S : Finset α)
    (z : α → Fin 3 → Point m n q)
    (hne : ∀ e ∈ S, (z e 0).2 ≠ (z e 1).2) :
    ∑ e ∈ S, rankWeight (z e) =
      ((S.card : ℝ) - (rankTwoTriples S z).card) / (q : ℝ)^(3*m) +
        (compatibleRankTwoTriples S z).card / (q : ℝ)^(2*m) := by
  have he : ∀ e ∈ S, rankWeight (z e) =
      1 / (q : ℝ)^(3*m) -
        (if (inputRows (z e)).rank = 2 then 1 / (q : ℝ)^(3*m) else 0) +
        (if (inputRows (z e)).rank = 2 ∧
          ∀ i, outputRows (z e) i ∈ LinearMap.range (inputRows (z e)).mulVecLin
          then 1 / (q : ℝ)^(2*m) else 0) := by
    intro e he
    rw [rankWeight_triple_cases (z e) (hne e he)]
    split_ifs <;> simp_all
  rw [Finset.sum_congr rfl he, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp only [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
    nsmul_eq_mul, rankTwoTriples, compatibleRankTwoTriples]
  ring

end SigabaNeo.Wall1.AffineGraphMoments
#print axioms SigabaNeo.Wall1.AffineGraphMoments.inputRows_rank_ge_two
#print axioms SigabaNeo.Wall1.AffineGraphMoments.inputRows_triple_rank_two_or_three

#print axioms SigabaNeo.Wall1.AffineGraphMoments.rankWeight_of_full_row_rank
#print axioms SigabaNeo.Wall1.AffineGraphMoments.rankWeight_triple_cases

#print axioms SigabaNeo.Wall1.AffineGraphMoments.sum_rankWeight_triples
