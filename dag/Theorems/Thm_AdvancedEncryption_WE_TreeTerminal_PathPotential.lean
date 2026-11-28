import Mathlib

theorem AdvancedEncryption.WE.TreeTerminal.PathPotential {R : Type*} [AddCommGroup R] (v : ℕ → R) (n : ℕ) :
    (∑ i ∈ Finset.range n, (v (i+1) - v i)) = v n - v 0 := by sorry
