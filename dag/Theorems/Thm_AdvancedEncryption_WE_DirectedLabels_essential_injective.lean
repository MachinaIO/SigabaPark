import Mathlib

open scoped BigOperators

theorem AdvancedEncryption.WE.DirectedLabels.essential_injective {I G : Type} [DecidableEq I] [AddCommGroup G] (v : I → G)
    (essential : ∀ i (A B : Finset I), i ∉ A → i ∉ B →
      v i ≠ (∑ j ∈ A, v j) - ∑ j ∈ B, v j) :
    Function.Injective (fun s : Finset I => ∑ i ∈ s, v i) := by sorry
