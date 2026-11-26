import Mathlib.Data.List.Basic

theorem solution {S B : Type} (h : S → B → S) (s0 : S)
    (n : ℕ) (s : S) :
    (∃ ws : List B, ws.length = n + 1 ∧ ws.foldl h s0 = s) ↔
      ∃ s' : S, (∃ ws : List B, ws.length = n ∧ ws.foldl h s0 = s') ∧ ∃ w : B, h s' w = s := by
  constructor
  · rintro ⟨ws, hl, rfl⟩
    obtain ⟨vs, w, rfl⟩ : ∃ vs w, ws = vs ++ [w] := by
      rcases List.eq_nil_or_concat ws with h0 | ⟨vs, w, hw⟩
      · subst h0; simp at hl
      · exact ⟨vs, w, by simpa using hw⟩
    refine ⟨vs.foldl h s0, ⟨vs, by simpa using hl, rfl⟩, w, by simp⟩
  · rintro ⟨s', ⟨vs, hl, rfl⟩, w, rfl⟩
    exact ⟨vs ++ [w], by simp [hl], by simp⟩
