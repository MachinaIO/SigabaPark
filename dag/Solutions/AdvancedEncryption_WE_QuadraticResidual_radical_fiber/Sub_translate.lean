import Mathlib

theorem solution {H G : Type} [AddCommGroup H] [AddCommGroup G] (D : H →+ G) (b : G) :
    ((∃ r, b + D r = 0) ↔ -b ∈ Set.range D) ∧
    ∀ r : H, b + D r = 0 → Nonempty ({s : H // b + D s = 0} ≃ D.ker) := by
  constructor
  · constructor
    · rintro ⟨r,h⟩
      exact ⟨r, by rw [eq_neg_iff_add_eq_zero]; simpa [add_comm] using h⟩
    · rintro ⟨r,h⟩
      exact ⟨r, by simp [h]⟩
  · intro r hr
    have hv : D r = -b := by rw [eq_neg_iff_add_eq_zero]; simpa [add_comm] using hr
    refine ⟨{
      toFun := fun s => ⟨s.1-r, by
        change D (s.1-r) = 0
        have hs : D s.1 = -b := by rw [eq_neg_iff_add_eq_zero]; simpa [add_comm] using s.2
        simp [map_sub,hs,hv]⟩
      invFun := fun s => ⟨s.1+r, by
        have hs : D s.1 = 0 := s.2
        simp [map_add,hs,hv]⟩
      left_inv := fun s => Subtype.ext (sub_add_cancel ..)
      right_inv := fun s => Subtype.ext (add_sub_cancel_right ..) }⟩
