import Mathlib

theorem solution (err p₀ p₁ sim : ℝ)
    (h₀ : p₀ ≤ err) (h₁ : 1 - err ≤ p₁) :
    1 / 2 - err ≤ max |p₀ - sim| |p₁ - sim| := by
  have hleft : sim - p₀ ≤ max |p₀ - sim| |p₁ - sim| := by
    calc
      sim - p₀ ≤ |sim - p₀| := le_abs_self _
      _ = |p₀ - sim| := abs_sub_comm _ _
      _ ≤ _ := le_max_left _ _
  have hright : p₁ - sim ≤ max |p₀ - sim| |p₁ - sim| :=
    (le_abs_self _).trans (le_max_right _ _)
  linarith
