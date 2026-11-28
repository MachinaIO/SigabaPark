import Mathlib

theorem solution (d m κ : ℕ) (enough : d + κ ≤ m) (prediction : (Fin d → Bool) → (Fin m → Bool)) :
    ((Finset.univ.image prediction).card : ℕ) * 2 ^ κ ≤ 2 ^ m := by
  have h := Finset.card_image_le (s := Finset.univ) (f := prediction)
  have h' : (Finset.univ.image prediction).card ≤ 2 ^ d := by simpa using h
  calc
    _ ≤ 2 ^ d * 2 ^ κ := Nat.mul_le_mul_right _ h'
    _ = 2 ^ (d + κ) := (pow_add _ _ _).symm
    _ ≤ _ := Nat.pow_le_pow_right (by decide) enough
