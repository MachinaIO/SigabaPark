import Mathlib

theorem AdvancedEncryption.WE.JoinRoute.two_join_closure {T : Type} [LinearOrder T] (A J C : T → Prop) :
    let outside := fun (U : T → Prop) (j : T) ↦
      (∃ i, U i ∧ i < j) ∨ (∃ i, U i ∧ j < i)
    let middle := fun j ↦ J j ∧ outside A j
    (∃ j, middle j ∧ outside C j) ↔
      ∃ i j k, A i ∧ J j ∧ C k ∧ i ≠ j ∧ k ≠ j := by
  sorry
