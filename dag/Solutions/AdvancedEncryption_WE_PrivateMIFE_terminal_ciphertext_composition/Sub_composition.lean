import Mathlib

theorem solution (width : ℕ → ℕ → ℕ) (w : ℕ)
    (base : ∀ s, w * s ≤ width 0 s)
    (nested : ∀ d s, width d (width d s) ≤ width (d + 1) s)
    (d s : ℕ) : w ^ (2 ^ d) * s ≤ width d s := by
  induction d generalizing s with
  | zero => simpa using base s
  | succ d ih =>
    calc
      w ^ (2 ^ (d+1)) * s = w ^ (2 ^ d) * (w ^ (2 ^ d) * s) := by
        rw [pow_succ 2 d, Nat.mul_two, pow_add, Nat.mul_assoc]
      _ ≤ w ^ (2 ^ d) * width d s := Nat.mul_le_mul_left _ (ih s)
      _ ≤ width d (width d s) := ih (width d s)
      _ ≤ width (d+1) s := nested d s
