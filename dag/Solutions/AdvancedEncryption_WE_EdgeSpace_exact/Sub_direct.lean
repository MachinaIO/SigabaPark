import Mathlib

open scoped BigOperators

theorem solution {ι V : Type} [Fintype ι] [AddCommGroup V]
    {W : ι → Type} [∀ i, AddCommGroup (W i)]
    (r : (i : ι) → V →+ W i) (s : V) :
    (∃ g : ι → V, ∑ i, g i = s ∧ ∀ i, r i (g i) = 0) ↔
    ∀ y : (i : ι) → W i, Nonempty
      (({a : ι → V // ∑ i, a i = 0 ∧ ∀ i, r i (a i) = y i}) ≃
       ({a : ι → V // ∑ i, a i = s ∧ ∀ i, r i (a i) = y i})) := by
  constructor
  · rintro ⟨g,hg,hzero⟩ y
    refine ⟨{ toFun := fun a => ⟨fun i => a.val i + g i, ?_, ?_⟩
              invFun := fun a => ⟨fun i => a.val i - g i, ?_, ?_⟩
              left_inv := ?_
              right_inv := ?_ }⟩
    · rw [Finset.sum_add_distrib, a.property.1, hg, zero_add]
    · intro i
      rw [map_add, a.property.2, hzero, add_zero]
    · rw [Finset.sum_sub_distrib, a.property.1, hg, sub_self]
    · intro i
      rw [map_sub, a.property.2, hzero, sub_zero]
    · intro a
      apply Subtype.ext
      funext i
      exact add_sub_cancel_right (a.val i) (g i)
    · intro a
      apply Subtype.ext
      funext i
      exact sub_add_cancel (a.val i) (g i)
  · intro h
    obtain ⟨e⟩ := h (fun _ => 0)
    let z : {a : ι → V // ∑ i, a i = 0 ∧ ∀ i, r i (a i) = 0} :=
      ⟨fun _ => 0, by simp, by simp⟩
    exact ⟨(e z).val,(e z).property⟩
