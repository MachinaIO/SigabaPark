import Mathlib

theorem solution {T : Type} [LinearOrder T] (A J C : T → Prop) :
    let outside := fun (U : T → Prop) (j : T) ↦
      (∃ i, U i ∧ i < j) ∨ (∃ i, U i ∧ j < i)
    let middle := fun j ↦ J j ∧ outside A j
    (∃ j, middle j ∧ outside C j) ↔
      ∃ i j k, A i ∧ J j ∧ C k ∧ i ≠ j ∧ k ≠ j := by
  dsimp only
  constructor
  · rintro ⟨j,⟨hj,ha⟩,hc⟩
    rcases ha with ⟨i,hi,lt⟩ | ⟨i,hi,gt⟩ <;>
      rcases hc with ⟨k,hk,lt'⟩ | ⟨k,hk,gt'⟩ <;>
      exact ⟨i,j,k,hi,hj,hk,by order,by order⟩
  · rintro ⟨i,j,k,hi,hj,hk,ne,ne'⟩
    refine ⟨j,⟨hj,?_⟩,?_⟩
    · rcases lt_or_gt_of_ne ne with h|h
      · exact Or.inl ⟨i,hi,h⟩
      · exact Or.inr ⟨i,hi,h⟩
    · rcases lt_or_gt_of_ne ne' with h|h
      · exact Or.inl ⟨k,hk,h⟩
      · exact Or.inr ⟨k,hk,h⟩
