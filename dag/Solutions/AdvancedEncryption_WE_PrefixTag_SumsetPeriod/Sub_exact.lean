import Mathlib

theorem solution {G : Type*} [AddCommGroup G] (S T : G → Prop) (h : G)
    (period : ∀ x, S (x+h) ↔ S x) (z : G) :
    (∃ a b, S a ∧ T b ∧ a+b = z+h) ↔ (∃ a b, S a ∧ T b ∧ a+b = z) := by
  constructor
  · rintro ⟨a,b,ha,hb,e⟩
    refine ⟨a-h,b,?_,hb,?_⟩
    · apply (period (a-h)).mp
      simpa using ha
    · rw [← add_right_cancel_iff (a := h)]
      calc
        (a-h+b)+h = a+b := by abel
        _ = z+h := e
  · rintro ⟨a,b,ha,hb,e⟩
    refine ⟨a+h,b,(period a).mpr ha,hb,?_⟩
    rw [← e]
    abel
