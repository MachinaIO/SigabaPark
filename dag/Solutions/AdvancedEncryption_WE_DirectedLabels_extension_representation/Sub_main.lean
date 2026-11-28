import Mathlib

open scoped BigOperators

theorem solution {I G : Type} [DecidableEq I] [AddCommGroup G]
    (v : I → G) (x : G) (inj : Function.Injective (fun s : Finset I => ∑ i ∈ s, v i))
    (A B : Finset I) (a b : Bool) (hne : (A,a) ≠ (B,b))
    (h : (∑ i ∈ A, v i) + (if a then x else 0) =
         (∑ i ∈ B, v i) + (if b then x else 0)) :
    (x = (∑ i ∈ A, v i) - ∑ i ∈ B, v i) ∨
    (x = (∑ i ∈ B, v i) - ∑ i ∈ A, v i) := by
  cases a <;> cases b <;> simp only [Bool.false_eq_true, ↓reduceIte, add_zero] at h
  · exact False.elim (hne (by rw [inj h]))
  · left; rw [h]; abel
  · right; rw [← h]; abel
  · exact False.elim (hne (by rw [inj (add_right_cancel h)]))
