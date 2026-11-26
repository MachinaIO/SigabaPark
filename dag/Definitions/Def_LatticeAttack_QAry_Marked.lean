module

public import SigabaNeoStd.Lattices.QAry

set_option autoImplicit true

public section

namespace SigabaNeo.QAry

open scoped NNReal

/-- Finite marked workloads on short tuples, grouped with their rational-rank weights. -/
theorem shortMeanValue {q m k : ℕ} [Fact q.Prime] {ι : Type*} (n : ℕ) (s : Finset ι)
    (X : ι → Matrix (Fin k) (Fin m) ℤ) (F : ι → ℝ≥0) (R : ℝ) (hR : 1 ≤ R)
    (hs : ∀ x ∈ s, ∀ i, ∑ j, (X x i j : ℝ)^2 ≤ R^2) (hq : R^k < q) :
    (∑ A : Fin n → Fin m → ZMod q, ∑ x ∈ s,
      if ∀ i, ((X x).map (Int.castRingHom (ZMod q))).mulVec (A i) = 0 then F x else 0) /
      (q : ℝ≥0)^(m*n) = ∑ x ∈ s, F x / (q : ℝ≥0)^(((X x).map (Int.castRingHom ℚ)).rank*n) := by
  rw [meanValue]
  exact Finset.sum_congr rfl fun x hx ↦ by rw [shortRank _ R hR (hs x hx) hq]

/-- Unnormalized Markov bound for a finite set of bad matrices with a witness mark. -/
theorem markedTail {α β : Type*} [Fintype α] (bad : Finset α) (marks : α → Finset β)
    (cost : α → β → ℝ≥0) (t : ℝ≥0)
    (witness : ∀ a ∈ bad, ∃ b ∈ marks a, t ≤ cost a b) :
    bad.card * t ≤ ∑ a, ∑ b ∈ marks a, cost a b := by
  classical
  calc
    _ = ∑ _a ∈ bad, t := by simp
    _ ≤ ∑ a ∈ bad, ∑ b ∈ marks a, cost a b := by
      apply Finset.sum_le_sum
      intro a ha
      obtain ⟨b, hb, h⟩ := witness a ha
      exact h.trans (Finset.single_le_sum (fun _ _ ↦ zero_le) hb)
    _ ≤ _ := Finset.sum_le_univ_sum_of_nonneg fun _ ↦ zero_le

#print axioms shortMeanValue
#print axioms markedTail

end SigabaNeo.QAry
