import Definitions.Def_RoleOrderLabels
import Mathlib.Tactic

theorem solution {V W : Type*} [AddCommGroup V] [AddCommGroup W] (f : V →+ W) (b : W) :
    (∀ y, (∃ k, f k = y) ↔ (∃ k, f k + b = y)) ↔ ∃ k, f k = b := by
  constructor
  · intro hs
    exact (hs b).mpr ⟨0,by simp⟩
  · rintro ⟨d,hd⟩ y
    constructor
    · rintro ⟨k,rfl⟩
      exact ⟨k-d,by simp [map_sub, hd]⟩
    · rintro ⟨k,rfl⟩
      exact ⟨k+d,by simp [map_add,hd]⟩
