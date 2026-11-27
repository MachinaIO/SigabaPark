import Mathlib
open scoped BigOperators

theorem solution (agg ordinary : ℕ → ℕ → ℕ)
    (ab : ∀ s, 4*s ≤ agg 0 s) (ob : ∀ s, s ≤ ordinary 0 s)
    (aa : ∀ d s, agg d (agg d s) ≤ agg (d+1) s)
    (ao : ∀ d s, agg d (ordinary d s) ≤ ordinary (d+1) s)
    (d s : ℕ) : 4^(2^d-1)*s ≤ ordinary d s := by
  have A (k z : ℕ) : 4^(2^k)*z ≤ agg k z := by
    induction k generalizing z with
    | zero => simpa using ab z
    | succ k ih =>
      calc
        4^(2^(k+1))*z = 4^(2^k)*(4^(2^k)*z) := by rw [pow_succ 2 k, Nat.mul_two, pow_add, Nat.mul_assoc]
        _ ≤ 4^(2^k)*agg k z := Nat.mul_le_mul_left _ (ih z)
        _ ≤ agg k (agg k z) := ih _
        _ ≤ _ := aa k z
  induction d generalizing s with
  | zero => simpa using ob s
  | succ d ih =>
    have ex : 2^(d+1)-1 = 2^d+(2^d-1) := by
      have hp : 0 < (2:ℕ)^d := by positivity
      rw [pow_succ]
      omega
    calc
      4^(2^(d+1)-1)*s = 4^(2^d)*(4^(2^d-1)*s) := by rw [ex,pow_add,Nat.mul_assoc]
      _ ≤ 4^(2^d)*ordinary d s := Nat.mul_le_mul_left _ (ih s)
      _ ≤ agg d (ordinary d s) := A _ _
      _ ≤ _ := ao d s
