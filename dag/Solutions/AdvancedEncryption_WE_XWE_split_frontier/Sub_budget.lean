import SigabaNeoStd

theorem solution (n e d h : ℕ) :
    (∃ a b c : ℕ, a + b + c = n ∧ max (a + c) b ≤ e ∧ max (max a b) c ≤ d ∧ b ≤ h) ↔
      n ≤ 2 * e ∧ n ≤ e + d ∧ n ≤ 3 * d ∧ n ≤ h + e ∧ n ≤ h + 2 * d := by
  constructor
  · rintro ⟨a, b, c, rfl, he, hd, hb⟩
    simp only [max_le_iff] at he hd
    omega
  · intro hcap
    let b := min n (min h (min e d))
    let a := min d (n - b)
    refine ⟨a, b, n - b - a, ?_⟩
    simp only [max_le_iff]
    dsimp [a, b]
    omega
