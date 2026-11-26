import Mathlib.Tactic.Linarith

theorem solution (m K1 K2 K3 E : ℕ) :
    (∃ a b c : ℕ, a + b + c = m ∧ a + K1 ≤ E ∧ b + K2 ≤ E ∧ c + K3 ≤ E) ↔
      m + K1 + K2 + K3 ≤ 3 * E ∧ K1 ≤ E ∧ K2 ≤ E ∧ K3 ≤ E := by
  constructor
  · rintro ⟨a, b, c, h, h1, h2, h3⟩
    omega
  · rintro ⟨h, h1, h2, h3⟩
    refine ⟨min (E - K1) m, min (E - K2) (m - min (E - K1) m),
      m - min (E - K1) m - min (E - K2) (m - min (E - K1) m), ?_, ?_, ?_, ?_⟩ <;> omega
