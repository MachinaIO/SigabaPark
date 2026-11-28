import Mathlib

theorem solution (v : Nat → Int) (score : Nat → Int) (initial : score 0 = 1-v 0-v 1)
    (pairStep : ∀ i, score (i+1) =
      score i + (v (2*i+2) + v (2*i+1) - 1) +
                (1-v (2*i+2)-v (2*i+3))) (k : Nat) :
    score k = 1-v 0-v (2*k+1) := by
  induction k with
  | zero => simpa using initial
  | succ k ih =>
    rw [pairStep, ih]
    have h : 2*(k+1)+1 = 2*k+3 := by omega
    rw [h]
    ring
