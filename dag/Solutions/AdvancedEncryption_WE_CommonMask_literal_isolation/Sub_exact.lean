import Mathlib

theorem solution {I K : Type} [Fintype I] [DecidableEq I] [Field K]
    (V : Submodule K ((I → Bool) → K))
    (one : (fun _ ↦ (1:K)) ∈ V)
    (keep : ∀ (i : I) (b : Bool) (f : (I → Bool) → K), f ∈ V →
      (fun w ↦ (if w i = b then (1:K) else 0) * f w) ∈ V) (a : I → Bool) :
    (fun w ↦ if w = a then (1:K) else 0) ∈ V := by
  classical
  have keepSet (s : Finset I) :
      (fun w ↦ ∏ i ∈ s, (if w i = a i then (1:K) else 0)) ∈ V := by
    induction s using Finset.induction_on with
    | empty => simpa using one
    | @insert i s hi ih =>
      simpa only [Finset.prod_insert hi] using keep i (a i) _ ih
  convert keepSet Finset.univ using 1
  funext w
  by_cases he : w = a
  · simp [he]
  · have hx : ∃ i, w i ≠ a i := by
      by_contra! h
      exact he (funext h)
    obtain ⟨i,hi⟩ := hx
    simp only [if_neg he]
    symm
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])
