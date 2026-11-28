import Mathlib

theorem AdvancedEncryption.WE.NoisyFiber.BinomialRotation (a b : ℚ) :
    let step : ℚ × ℚ → ℚ × ℚ := fun v ↦ ((v.1-v.2)/2,(v.1+v.2)/2)
    let q := step (step (a,b))
    |q.1| + |q.2| = (|a|+|b|)/2 := by sorry
