module

public import Definitions.Def_LatticeAttack_QAry_Marked

set_option autoImplicit true

public section

namespace SigabaNeo.QAry

open scoped NNReal

/-- One-sided mean-value transfer, charging discrepant ranks at their full modular weight. -/
theorem meanValue_le_add_defect {q m k : ℕ} [Fact q.Prime] {ι : Type*} [DecidableEq ι]
    (n : ℕ) (S D : Finset ι) (X : ι → Matrix (Fin k) (Fin m) (ZMod q))
    (r : ι → ℕ) (F : ι → ℝ≥0) (h : ∀ x ∈ S, x ∉ D → (X x).rank = r x) :
    (∑ A : Fin n → Fin m → ZMod q, ∑ x ∈ S,
      if ∀ i, (X x).mulVec (A i) = 0 then F x else 0) / (q : ℝ≥0) ^ (m * n) ≤
    (∑ x ∈ S, F x / (q : ℝ≥0) ^ (r x * n)) +
      ∑ x ∈ D, F x / (q : ℝ≥0) ^ ((X x).rank * n) := by
  classical
  rw [meanValue]
  calc
    _ = (∑ x ∈ S \ D, F x / (q : ℝ≥0) ^ ((X x).rank * n)) +
        ∑ x ∈ S ∩ D, F x / (q : ℝ≥0) ^ ((X x).rank * n) :=
      by rw [← Finset.sum_union (Finset.disjoint_sdiff_inter _ _), Finset.sdiff_union_inter]
    _ ≤ _ := by
      apply add_le_add
      · calc
          _ = ∑ x ∈ S \ D, F x / (q : ℝ≥0) ^ (r x * n) := by
            apply Finset.sum_congr rfl
            intro x hx
            rw [h x (Finset.mem_sdiff.mp hx).1 (Finset.mem_sdiff.mp hx).2]
          _ ≤ _ := Finset.sum_le_sum_of_subset Finset.sdiff_subset
      · exact Finset.sum_le_sum_of_subset Finset.inter_subset_right

#print axioms meanValue_le_add_defect

end SigabaNeo.QAry
