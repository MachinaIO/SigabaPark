import Definitions.Def_WE_MaskedGGH15

open AdvancedEncryption.WE.MaskedGGH15

theorem solution {w h : ℕ} (Ψ : CNF w h)
    (a b : Fin h) (hab : a ≠ b) (j : Fin w)
    (hj : ∀ (l : Fin h) (c : Bool), Ψ j l c = true ↔ ((l = a ∧ c = true) ∨ (l = b ∧ c = false)))
    (c : Bool) : cnfMat Ψ b c j j + cnfMat Ψ b (!c) j j = 1 := by
  have hb : ∀ d : Bool, Ψ j b d = !d := by
    intro d
    have hd := hj b d
    cases d
    · simpa using hd
    · cases hΨ : Ψ j b true
      · rfl
      · have := hd.mp hΨ
        simp at this
        exact absurd this.symm hab
  simp only [cnfMat, Matrix.diagonal_apply_eq, hb]
  cases c <;> simp
