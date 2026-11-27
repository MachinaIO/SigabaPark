import Definitions.Def_TerminalRectangle

open TerminalRectangle

theorem solution {I : Type} (A J C : Set I) :
    ¬ Wins A J C ↔ ∀ j ∈ J, (∀ i ∈ A, i = j) ∨ (∀ k ∈ C, k = j) := by
  classical
  constructor
  · intro hl j hj
    by_cases ha : ∀ i ∈ A, i = j
    · exact Or.inl ha
    · right
      push_neg at ha
      obtain ⟨i, hi, hij⟩ := ha
      intro k hk
      by_contra hkj
      exact hl ⟨i, hi, j, hj, k, hk, hij, hkj⟩
  · rintro hh ⟨i, hi, j, hj, k, hk, hij, hkj⟩
    rcases hh j hj with ha | hc
    · exact hij (ha i hi)
    · exact hkj (hc k hk)
