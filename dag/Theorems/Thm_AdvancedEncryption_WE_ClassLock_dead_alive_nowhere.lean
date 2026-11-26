import Mathlib.Tactic.Common

/-- A slot program with both entries 0 at some level is alive on no string (note `pq-we-class-lock`). -/
theorem AdvancedEncryption.WE.ClassLock.dead_alive_nowhere (m : ℕ → Bool → Bool) (j : ℕ) (hdead : ∀ β, m j β = false)
    (x : ℕ → Bool) : ¬ ∀ i, m i (x i) = true := by sorry
