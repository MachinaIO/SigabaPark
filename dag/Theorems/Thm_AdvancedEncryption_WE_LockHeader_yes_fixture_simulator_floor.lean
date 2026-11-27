import Mathlib

theorem AdvancedEncryption.WE.LockHeader.yes_fixture_simulator_floor (err p₀ p₁ sim : ℝ)
    (h₀ : p₀ ≤ err) (h₁ : 1 - err ≤ p₁) :
    1 / 2 - err ≤ max |p₀ - sim| |p₁ - sim| := by sorry
