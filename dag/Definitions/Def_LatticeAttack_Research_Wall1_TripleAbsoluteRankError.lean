import Definitions.Def_LatticeAttack_Research_Wall1_AffineTripleRank

set_option autoImplicit true

/-! Absolute triple rank errors, without cancellation between candidates. -/
noncomputable section
namespace SigabaNeo.Wall1.AffineGraphMoments
open Finset
open scoped Classical
variable {q m n : ℕ} [Fact q.Prime]

theorem rankWeight_triple_abs_error (z : Fin 3 → Point m n q)
    (hne : (z 0).2 ≠ (z 1).2) :
    |rankWeight z - 1 / (q : ℝ)^(3*m)| ≤
      (if (inputRows z).rank = 2 then 1 / (q : ℝ)^(3*m) else 0) +
      (if (inputRows z).rank = 2 ∧
        ∀ i, outputRows z i ∈ LinearMap.range (inputRows z).mulVecLin
        then 1 / (q : ℝ)^(2*m) else 0) := by
  rw [rankWeight_triple_cases z hne]
  split_ifs <;> simp_all
  apply (abs_sub _ _).trans_eq
  rw [abs_of_nonneg (by positivity : 0 ≤ ((q : ℝ)^(2*m))⁻¹),
    abs_of_nonneg (by positivity : 0 ≤ ((q : ℝ)^(3*m))⁻¹)]
  ring

/-- Both exceptional masses are retained; this bound uses no signed cancellation. -/
theorem sum_rankWeight_triple_abs_error {α : Type*} (S : Finset α)
    (z : α → Fin 3 → Point m n q)
    (hne : ∀ e ∈ S, (z e 0).2 ≠ (z e 1).2) :
    ∑ e ∈ S, |rankWeight (z e) - 1 / (q : ℝ)^(3*m)| ≤
      ((rankTwoTriples S z).card : ℝ) / (q : ℝ)^(3*m) +
        (compatibleRankTwoTriples S z).card / (q : ℝ)^(2*m) := by
  apply (sum_le_sum (fun e he ↦ rankWeight_triple_abs_error (z e) (hne e he))).trans_eq
  rw [sum_add_distrib]
  simp only [sum_ite, sum_const_zero, add_zero, sum_const, nsmul_eq_mul,
    rankTwoTriples, compatibleRankTwoTriples]
  ring

end SigabaNeo.Wall1.AffineGraphMoments
#print axioms SigabaNeo.Wall1.AffineGraphMoments.sum_rankWeight_triple_abs_error
