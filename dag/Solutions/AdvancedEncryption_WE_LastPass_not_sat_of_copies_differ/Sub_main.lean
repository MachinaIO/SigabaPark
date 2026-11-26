import Definitions.Def_WE_MaskedGGH15

open AdvancedEncryption.WE.MaskedGGH15

theorem solution {w h : ℕ} (Ψ : CNF w h)
    (a b : Fin h)
    (h1 : ∃ j : Fin w, ∀ (l : Fin h) (c : Bool), Ψ j l c = true ↔
      ((l = a ∧ c = true) ∨ (l = b ∧ c = false)))
    (h2 : ∃ j : Fin w, ∀ (l : Fin h) (c : Bool), Ψ j l c = true ↔
      ((l = a ∧ c = false) ∨ (l = b ∧ c = true)))
    (z : Fin h → Bool) (hz : z a ≠ z b) : ¬ Sat Ψ z := by
  intro hsat
  obtain ⟨j1, hj1⟩ := h1
  obtain ⟨j2, hj2⟩ := h2
  cases ha : z a with
  | true =>
    have hb : z b = false := by
      cases hb' : z b
      · rfl
      · exact absurd (ha.trans hb'.symm) hz
    obtain ⟨i, hi⟩ := hsat j2
    rcases (hj2 i (z i)).mp hi with ⟨rfl, hzi⟩ | ⟨rfl, hzi⟩
    · rw [ha] at hzi; exact Bool.noConfusion hzi
    · rw [hb] at hzi; exact Bool.noConfusion hzi
  | false =>
    have hb : z b = true := by
      cases hb' : z b
      · exact absurd (ha.trans hb'.symm) hz
      · rfl
    obtain ⟨i, hi⟩ := hsat j1
    rcases (hj1 i (z i)).mp hi with ⟨rfl, hzi⟩ | ⟨rfl, hzi⟩
    · rw [ha] at hzi; exact Bool.noConfusion hzi
    · rw [hb] at hzi; exact Bool.noConfusion hzi
