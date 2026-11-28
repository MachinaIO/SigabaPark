import Mathlib

theorem AdvancedEncryption.WE.TreeTerminal.UniformParityProgramming (p b t : ℕ) (hp : 2 ∣ p) :
    (t < p ∧ (b+t)%2 = 1) ↔
    ∃! j : ℕ, j < p/2 ∧ t = 2*j+(b+1)%2 := by sorry
