import Mathlib.Tactic.Ring

theorem solution
    {F : Type*} [CommRing F] [IsDomain F] (h₂ : (2 : F) ≠ 0) (a b c d : F) :
    (a + b = c + d ∧ a ^ 2 + b ^ 2 = c ^ 2 + d ^ 2) ↔
      (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  constructor
  · rintro ⟨h, hs⟩
    have hd : d = a + b - c := by rw [h]; simp
    rw [hd] at hs
    have e : 2 * ((a - c) * (b - c)) = 0 := calc
      _ = c ^ 2 + (a + b - c) ^ 2 - (a ^ 2 + b ^ 2) := by ring
      _ = 0 := by rw [hs]; simp
    rcases mul_eq_zero.mp ((mul_eq_zero.mp e).resolve_left h₂) with hac | hbc
    · have ha := sub_eq_zero.mp hac
      exact Or.inl ⟨ha, by simpa [ha, add_comm] using hd.symm⟩
    · have hb := sub_eq_zero.mp hbc
      exact Or.inr ⟨by simpa [hb] using hd.symm, hb⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> simp [add_comm]
