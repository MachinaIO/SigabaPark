import Mathlib

open scoped BigOperators

theorem AdvancedEncryption.WE.DirectedLabels.subset_sum_size {I G : Type} [Fintype I] [Fintype G] [DecidableEq I] [AddCommGroup G]
    (v : I → G) (inj : Function.Injective (fun s : Finset I => ∑ i ∈ s, v i)) :
    2 ^ Fintype.card I ≤ Fintype.card G := by sorry
