import Mathlib

open scoped BigOperators

theorem solution {I G : Type} [DecidableEq I] [AddCommGroup G] (v : I → G)
    (essential : ∀ i (A B : Finset I), i ∉ A → i ∉ B →
      v i ≠ (∑ j ∈ A, v j) - ∑ j ∈ B, v j) :
    Function.Injective (fun s : Finset I => ∑ i ∈ s, v i) := by
  intro A B h
  change (∑ j ∈ A, v j) = ∑ j ∈ B, v j at h
  have sub : ∀ P Q : Finset I, (∑ j ∈ P, v j) = ∑ j ∈ Q, v j → P ⊆ Q := by
    intro P Q e i hi
    by_contra hn
    apply essential i Q (P.erase i) hn (Finset.notMem_erase _ _)
    rw [← e, ← Finset.sum_erase_add _ _ hi]
    abel
  exact Finset.Subset.antisymm (sub A B h) (sub B A h.symm)
