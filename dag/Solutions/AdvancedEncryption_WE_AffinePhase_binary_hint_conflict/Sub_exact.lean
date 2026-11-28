import Mathlib

theorem solution (f : ℤ → Bool) (h : ℕ) :
    ∃ z : ℤ, f z = f (z+h) ∨ f z = f (z+h+1) := by
  by_contra! hn
  have adjacent (z : ℤ) : f (z+1) = f z := by
    have a := (hn (z+1)).1
    have b := (hn z).2
    rw [show z + 1 + (h:ℤ) = z+h+1 by ring] at a
    cases h₀ : f (z+1) <;> cases h₁ : f z <;> cases h₂ : f (z+h+1) <;> simp_all
  have same (n : ℕ) : f (n:ℤ) = f 0 := by
    induction n with
    | zero => rfl
    | succ n ih => simpa using (adjacent (n:ℤ)).trans ih
  exact (hn 0).1 (by simpa using (same h).symm)
